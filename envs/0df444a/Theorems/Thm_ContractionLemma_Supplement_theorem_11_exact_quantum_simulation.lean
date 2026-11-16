-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_11_exact_quantum_simulation
-- name    : ContractionLemma.Supplement.theorem_11_exact_quantum_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:27:39.320441+00:00
-- url     : https://prove2.me/theorems/92515373-327d-4ac9-b013-d4eed9d22382
-- title:
--   Theorem 11, p.38 — exact acceptance probability of a quantum circuit in a fixed number field in time $\mathrm{poly}(L+s+q)E(s+q)$
-- statement:
--   Fix a finite gate set $\mathcal G$ of constant-arity unitary gates with algebraic entries, such as Hadamard and Toffoli, or Clifford+T. There are an algebraic integer $\alpha$, of degree $d$, depending only on $\mathcal G$, and deterministic algorithms that, for every circuit $Q$ over $\mathcal G$ with $s$ gates on $q$ qubits and a computational-basis input (description length $L$), run in time $\mathrm{poly}(L+s+q)\,E(s+q)$ and polynomial space and compute:
--
--   1. the acceptance probability exactly, as its coordinates $r_0,\dots,r_{d-1}\in\mathbb Q$ with
--   $$
--   \Pr[\text{accept}]=\sum_{j<d} r_j\,\alpha^j\in\mathbb Q(\alpha);
--   $$
--   2. for any given rational $\theta$, the exact comparison of $\Pr[\text{accept}]$ with $\theta$;
--   3. if a postselection event has positive probability, the coordinates of the conditional acceptance probability given it.
--
--   Quantum computation is thereby simulated exactly, with no error, in time subexponential in the size of the circuit.
--
--   Differences from the source:
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: "as an element of a fixed number field" → rational coordinates in the basis $1,\alpha,\dots,\alpha^{d-1}$ of $\mathbb Q(\alpha)$, $\alpha$ an algebraic integer of degree $d$ fixed by the gate set; the comparison outputs the two bits $[p\le\theta]$, $[\theta\le p]$; reason: Lean representation of an element of $\mathbb Q(\alpha)$ (as in Lemma 2.6) and of an exact comparison
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 11, p.38 (stated first on p.8); §2.5, p.20; proof pp.38–39

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_Quantum

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open scoped Classical
/-- **Theorem 11 (Exact quantum simulation)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.38 (PDF p.41; stated first on p.8).

"Fix a finite gate set of constant-arity gates with algebraic entries, such as Hadamard and Toffoli,
or Clifford+T. Let `Q` be a circuit over this gate set with `s` gates on `q` qubits and a
computational-basis input. Its acceptance probability can be computed exactly, as an element of a
fixed number field, in time `poly(L + s + q) E(s + q)`. In the same time it can be compared exactly
with any rational threshold, and the acceptance probability conditioned on a postselection event of
positive probability can be computed exactly."

For every gate set `G` there are an algebraic integer `α` with minimal polynomial of degree `d`
(the number field `ℚ(α)` is fixed by `G`), machines and a constant `C` such that, for every circuit
`Q` over `G` (length `L` of its encoding, `s` gates, `q` qubits), in time
`C (L'+s+q+1)^C 2^{C f(s+q)}` and space `C (L'+s+q+1)^C`, `L'` the input length:

1. one machine outputs the coordinates `r_0, …, r_{d−1} ∈ ℚ` of `Pr[accept] = ∑_j r_j α^j`;
2. one machine, given `Q` and a rational `θ`, outputs the two bits `[Pr[accept] ≤ θ]`,
   `[θ ≤ Pr[accept]]`;
3. one machine, given `Q` whose postselection event has positive probability, outputs the
   coordinates of `Pr[accept | post]`.

**Formalization Note.** Probabilities are computed from the state `g_s ⋯ g_1 |x⟩` in
`(Fin q → Bool) → ℂ`. The coordinates in the basis `1, α, …, α^{d−1}` are unique because `d` is the
degree of `α`. `f(u) = u/√log₂(u+2)`. The polynomial-space clause is the paper's convention (p.3). -/
theorem theorem_11_exact_quantum_simulation (G : GateSet) :
    ∃ (α : ℂ) (d : ℕ), IsIntegral ℤ α ∧ (minpoly ℚ α).natDegree = d ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ Q : QCircuit G,
      ∃ r : Fin d → ℚ, (∑ j, (r j : ℂ) * α ^ (j : ℕ)) = (Q.accProb : ℂ) ∧
        ContractionLemma.RunsWithin A out Q.encode (Encoding.encodeList ratWord (List.ofFn r))
          (C * ((Q.encode.length : ℝ) + Q.size + Q.q + 1) ^ C * (2 : ℝ) ^ (C * fScale (Q.size + Q.q)))
          (C * ((Q.encode.length : ℝ) + Q.size + Q.q + 1) ^ C)) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ (Q : QCircuit G) (θ : ℚ),
      ContractionLemma.RunsWithin A out (Encoding.encodeList id [Q.encode, ratWord θ])
        [decide (Q.accProb ≤ θ), decide ((θ : ℝ) ≤ Q.accProb)]
        (C * (((Encoding.encodeList id [Q.encode, ratWord θ]).length : ℝ) + Q.size + Q.q + 1) ^ C *
          (2 : ℝ) ^ (C * fScale (Q.size + Q.q)))
        (C * (((Encoding.encodeList id [Q.encode, ratWord θ]).length : ℝ) + Q.size + Q.q + 1) ^ C)) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ Q : QCircuit G, 0 < Q.postProb →
      ∃ r : Fin d → ℚ, (∑ j, (r j : ℂ) * α ^ (j : ℕ)) = ((Q.accPostProb / Q.postProb : ℝ) : ℂ) ∧
        ContractionLemma.RunsWithin A out Q.encode (Encoding.encodeList ratWord (List.ofFn r))
          (C * ((Q.encode.length : ℝ) + Q.size + Q.q + 1) ^ C * (2 : ℝ) ^ (C * fScale (Q.size + Q.q)))
          (C * ((Q.encode.length : ℝ) + Q.size + Q.q + 1) ^ C)) := by sorry

end ContractionLemma.Supplement
