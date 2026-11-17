-- Prove2me | Theorems.Thm_DepthOptQC_Synth_Supplement_theorem_11
-- name    : DepthOptQC.Synth.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:49:40.756595+00:00
-- url     : https://prove2.me/theorems/372374de-43b7-4368-987d-a9a92e28cd90
-- title:
--   Theorem 11 — additive-depth catalytic universalization of QNCf
-- statement:
--   There are uniform constants $K>0$ and $k\in\mathbb N$ with the following property. Let $C$ be a size-$s$, depth-$D$ QNCf circuit. After exactly decomposing its one-qubit gates, up to one global phase, into Hadamard and phase gates, let $r$ be the total number of phase gates and $w$ the maximum number in one layer. For every $\delta\in(0,1)$ there is a QUNCf circuit $\widetilde C$ using $A$ fresh clean ancillas such that, for one phase $\varphi$ and every input $|\psi\rangle$,
--   $$
--   \|\widetilde C(|\psi\rangle|0^A\rangle)-e^{i\varphi}(C|\psi\rangle)|0^A\rangle\|_2
--   \le\delta\|\psi\|_2.
--   $$
--   Its depth is at most
--   $$K\bigl(D+1+\log_2\log_2((r+w+2)/\delta)\bigr),$$
--   and its size and clean workspace are at most $K(s+1/\delta)^k$.
--
--   The additive term is paid once to prepare and unprepare the catalyst bank, not once per circuit layer.
--
--   Differences from the source:
--   - reading: $O(D+\log\log((r+w+2)/\delta))$ and polynomial costs → uniform witnesses $K,k$, with $1+\log_2\log_2$ as the positive representative; reason: explicit uniform asymptotics over the full printed precision range
--   - encoding: "after decomposing" and then defining $r,w$ → `IsPhaseDecomposition` computes both counts from an exact Hadamard/phase circuit with the paper's fivefold Euler-expansion resource bounds; reason: prevents unrelated count parameters and preserves the source construction
--   - generalization: the source uses the gate-by-gate Euler decomposition → Lean permits any unitary-equivalent Hadamard/phase decomposition with at most fivefold depth and size; reason: the paper's decomposition is included, and its catalyst argument uses only exact equivalence, the two resource bounds, and the resulting counts
--   - encoding: the paper writes clean ancillas first → Lean appends them after the data wires; reason: fixed wire relabelling
--   - encoding: the paper quantifies normalized inputs → Lean quantifies every vector with error $\delta\|\psi\|_2$; reason: homogeneity of the two linear maps makes this exactly equivalent, including the zero vector
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 11, pp.45–47 (PDF pp.47–49), Eqs. (215)–(216)

import Definitions.Def_DepthOptQC_Synth_Supplement_CircuitModel

set_option autoImplicit false

namespace DepthOptQC.Synth.Supplement

open QAlgorithms DepthOptQC.Synth

/-- **Theorem 11 (Additive-Depth Catalytic Universalization)** — Vasconcelos,
arXiv:2609.34659, p.45, Eqs. (215)–(216). A QNCf circuit whose Hadamard/phase decomposition has
`r` phase gates and at most `w` phase gates in one layer admits a clean QUNCf simulation whose
only non-depth-preserving cost is one additive doubly-logarithmic catalyst-preparation term.

**Formalization Note.** `IsPhaseDecomposition` computes `r,w` from an actual exact decomposition,
so they cannot be chosen independently of the source circuit. `1+log₂log₂` is the positive
uniform representative of the printed asymptotic logarithm. -/
theorem theorem_11 :
    ∃ K : ℝ, 0 < K ∧ ∃ k : ℕ,
      ∀ (n s D r w : ℕ) (C : LayeredCircuit qncfGateSet n),
        C.size = s → C.depth = D → IsPhaseDecomposition C r w →
        ∀ δ : ℝ, 0 < δ → δ < 1 →
          ∃ A : ℕ, ∃ Ctilde : LayeredCircuit quncfGateSet (n + A),
            CleanlyApproximatesCircuit Ctilde.unitary C.unitary δ ∧
            (Ctilde.depth : ℝ) ≤
              K * ((D : ℝ) + loglogScale (((r + w + 2 : ℕ) : ℝ) / δ)) ∧
            (Ctilde.size : ℝ) ≤ K * ((s : ℝ) + 1 / δ) ^ k ∧
            (A : ℝ) ≤ K * ((s : ℝ) + 1 / δ) ^ k := by sorry

end DepthOptQC.Synth.Supplement
