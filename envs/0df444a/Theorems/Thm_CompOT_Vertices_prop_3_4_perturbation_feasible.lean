-- Prove2me | Theorems.Thm_CompOT_Vertices_prop_3_4_perturbation_feasible
-- name    : CompOT.Vertices.prop_3_4_perturbation_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:39.947697+00:00
-- url     : https://prove2.me/theorems/19f2ab1b-1807-422e-b211-96f8e164f7c3
-- title:
--   Proof of Proposition 3.4, p. 407 — P ± tE stays in U(a, b) for a small step t > 0
-- statement:
--   Let $a \in \Sigma_n$, $b \in \Sigma_m$ be the book's histograms and $P \in U(a,b)$. Let $E \in \mathbb R^{n\times m}$ have zero row sums and zero column sums, $E\mathbb 1_m = 0_n$ and $E^\top \mathbb 1_n = 0_m$, and be supported on the support of $P$: $E_{ij} \ne 0$ implies $P_{ij} > 0$. Then there is $t > 0$ such that
--   $$Q = P + tE \in U(a,b) \qquad\text{and}\qquad R = P - tE \in U(a,b).$$
--
--   Since $P = (Q+R)/2$, a nonzero such $E$ shows that $P$ is not an extremal point of $U(a,b)$. This is the feasibility half of the proof of Proposition 3.4.
--
--   **Formalization Note** The simplex hypotheses are the book's standing notation (p. 360). The step $t$ plays the role of the book's "elementary amount of flow" $\varepsilon < \min_{(i,j') \in S(P)} P_{ij}$.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.4.1, proof of Proposition 3.4, p. 407 (Q = P + E and R = P − E are feasible)

import Mathlib
import Definitions.Def_CompOT_Vertices_Defs

namespace CompOT.Vertices

/-- Proof of Proposition 3.4, p. 407: for histograms `a ∈ Σₙ`, `b ∈ Σₘ`, a perturbation matrix `E` with zero row sums
(`E 𝟙_m = 0_n`), zero column sums (`Eᵀ 𝟙_n = 0_m`) and supported on the support of `P`
can be added to and subtracted from a coupling `P ∈ U(a, b)` with a small enough positive
step `t` (the book's "elementary amount of flow" `ε`), and both `Q = P + tE` and
`R = P − tE` stay in `U(a, b)`. -/
theorem prop_3_4_perturbation_feasible {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P E : Matrix (Fin n) (Fin m) ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (hP : P ∈ CompOT.Assignment.couplings a b)
    (hrow : ∀ i, ∑ j, E i j = 0) (hcol : ∀ j, ∑ i, E i j = 0)
    (hsupp : ∀ i j, E i j ≠ 0 → 0 < P i j) :
    ∃ t : ℝ, 0 < t ∧ P + t • E ∈ CompOT.Assignment.couplings a b ∧ P - t • E ∈ CompOT.Assignment.couplings a b := by sorry

end CompOT.Vertices
