-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_48
-- name    : CatalystQLB.Query.eq_48
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:05.909014+00:00
-- url     : https://prove2.me/theorems/7a4bf8c4-dbc9-4f18-80d7-48ffa6c9f23f
-- title:
--   Eq. (48) — success probability of the inverter built from a circuit
-- statement:
--   Let an oracle circuit make $q-1\ge1$ queries to $O_f$ and $q_g$ queries to $O_g$, and let $\Pi=|g(x)\rangle\langle g(x)|_Q\otimes I_{RC}$. There is an inverter $\mathcal I$, depending only on the circuit, that receives $z=g(x)$, makes at most $q_g$ queries to $O_g$ and none to $O_f$, and satisfies
--   $$\mathrm{succ}_{\mathrm{inv}}=\frac{1}{(q-1)2^{\lambda+\ell}}\,\mathbb E_{f,g,x}\sum_{i=1}^{q-1}\mathrm{tr}\big[(|x\rangle\langle x|_Q\otimes I_{RC})\,Z_i^\dagger\Pi Z_i\big]\ \ge\ \frac{1}{(q-1)2^{\ell}}\,\mathbb E_{f,g,x}\sum_{i=1}^{q-1}\big\|\Pi Z_i\,|x,f(g(x)),0^\ell\rangle\big\|^2.$$
--
--   The inverter guesses the branch $i$, simulates its own random $f$, runs $Z_i^\dagger$ on $|z\rangle\langle z|\otimes I/2^{\lambda+\ell}$ with abort tests, and measures $Q$. The bound turns a large total branch weight into a good inverter.
--
--   **Formalization Note** The average over $f$ on the right reflects the inverter's own uniformly sampled $f$; the inverter is never given $x$ or the true $f$.
--
--   Differences from the source:
--   - reading: the inversion algorithm $\mathcal I$ (receives $z=g(x)$, queries $O_g$, samples its own $i$ and $f$, runs the tests $\{\Pi^\perp,\Pi\}$, measures $Q$, may abort) → `Inverter n W T`: for each $z$ a $T$-query `QAlgorithms.QueryAlg` on $(Q\times R)\times W$ with an arbitrary finite workspace $W$, a final computational-basis measurement and an output map to `Option` strings (`none` = abort); reason: randomness and intermediate measurements are purified into the workspace (deferred measurement), so the class contains the paper's inverter; the inverter never gets $x$ or $O_f$
--   - encoding: “the total number of queries to $g$ is at most $q_g$” → an inverter with exactly $T$ queries and $T\le q_g$; reason: same class of inverters
--   - encoding: the four-member display (48) → its first equality and its final inequality; reason: the omitted members rewrite the same quantity ($I_C=|0^\ell\rangle\langle0^\ell|+\Pi'_\ell$) and are implied by the stated first and last relations
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
--   - encoding: $\mathbb E_{f,g,x}$ and $\mathrm{tr}[\cdot]$ of positive operators → normalized finite sums (`expectFGX`) and the real part of the matrix trace; reason: Lean convention; for the positive operators to which the source applies the formulas the trace is real, so no instance changes
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (48), pp.46–47 (PDF 49–50); Eq. (57), p.50 (PDF 53)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit_branchZ
import Definitions.Def_CatalystQLB_Query_Inverter
import Definitions.Def_CatalystQLB_Query_expectFGX

open scoped Matrix

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eq. (48)**, the inverter's success (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §5.3, Lemma 75's proof, Step (2), pp.46–47
(PDF 49–50); restated as Eq. (57), p.50). Let the circuit make `q − 1 = numF C ≥ 1` queries to
`O_f` and `q_g = numG C` to `O_g`, and `Π = |g(x)⟩⟨g(x)|_Q ⊗ I_RC`. There is an inverter
making at most `q_g` queries to `O_g` (and none to `O_f`; it is not given `x`) with
`succ_inv = 1/((q−1)2^{n+ℓ}) E_{f,g,x} Σ_{i=1}^{q−1} tr[(|x⟩⟨x|_Q ⊗ I_RC) Z_i† Π Z_i]
  ≥ 1/((q−1)2^ℓ) E_{f,g,x} Σ_{i=1}^{q−1} ‖Π Z_i |x, f(g(x)), 0^ℓ⟩‖²`.

**Formalization Note** `n` is `λ`. The inverter is one object for all `g` and `x` (it
depends only on the circuit); the average over `f` on the right reflects the inverter's own
uniformly sampled `f`. Real parts of the traces; `|x, f(g(x)), 0^ℓ⟩` is
`ket ((x, f (g x)), 0)`. -/
theorem eq_48 {n ℓ : ℕ} (C : OracleCircuit n ℓ) (hq : 1 ≤ C.numF) :
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (T : ℕ) (I : Inverter n W T),
      T ≤ C.numG ∧
      I.invSuccess = ((C.numF : ℝ) * 2 ^ (n + ℓ))⁻¹ * expectFGX n (fun f g x =>
        ∑ i ∈ Finset.Icc 1 C.numF, (Matrix.trace
          (Matrix.kronecker (Matrix.kronecker (Matrix.single x x (1 : ℂ))
              (1 : Matrix (Qubits n) (Qubits n) ℂ)) (1 : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) *
            (C.branchZ f g x i)ᴴ * firstQueryProj (g x) * C.branchZ f g x i)).re) ∧
      ((C.numF : ℝ) * 2 ^ ℓ)⁻¹ * expectFGX n (fun f g x =>
        ∑ i ∈ Finset.Icc 1 C.numF,
          ‖act (firstQueryProj (g x) * C.branchZ f g x i)
            (ket (((x, f (g x)), (0 : Qubits ℓ)) : Idx n ℓ))‖ ^ 2) ≤ I.invSuccess := by sorry

end CatalystQLB.Query
