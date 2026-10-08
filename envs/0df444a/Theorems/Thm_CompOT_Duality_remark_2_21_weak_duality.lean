-- Prove2me | Theorems.Thm_CompOT_Duality_remark_2_21_weak_duality
-- name    : CompOT.Duality.remark_2_21_weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:48.955406+00:00
-- url     : https://prove2.me/theorems/61874858-f595-4d89-af57-fc8b60dd60b6
-- title:
--   Remark 2.21, p. 385 — weak duality: ⟨C, P⟩ ≥ Σ P_{ij}(f_i + g_j) = ⟨f, a⟩ + ⟨g, b⟩
-- statement:
--   Let $a \in \Sigma_n$ and $b \in \Sigma_m$ be histograms (nonnegative vectors summing to $1$), let $C \in \mathbb R^{n\times m}$, let $P \in \mathbf U(a,b)$ be a transport plan and let $(f,g) \in \mathbf R(C)$, i.e. $f_i + g_j \le C_{i,j}$ for all $i,j$. Then
--   $$\sum_{i,j} P_{i,j}C_{i,j} \;\ge\; \sum_{i,j} P_{i,j}(f_i+g_j) \;=\; \Big(\sum_i f_i \sum_j P_{i,j}\Big) + \Big(\sum_j g_j \sum_i P_{i,j}\Big) \;=\; \langle f,a\rangle + \langle g,b\rangle.$$
--
--   This is the easy half of Kantorovich duality: every admissible pair of prices $(f,g)$ gives a lower bound on the cost of every transport plan, hence on $L_C(a,b)$.
--
--   **Formalization Note** The three relations of the display are stated as a conjunction, with the sums written explicitly. The histogram hypotheses $a \in \Sigma_n$, $b \in \Sigma_m$ are the book's standing convention for $(a,b)$ (notation section, and (2.11)).
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Remark 2.21, display on p. 385 (preceding text on p. 384)

import Mathlib
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.Duality

/-- Remark 2.21, display on p. 385: for a transport plan `P ∈ U(a, b)` and prices
`(f, g) ∈ R(C)`, `∑ P_{ij} C_{ij} ≥ ∑ P_{ij} (f_i + g_j) = (∑_i f_i ∑_j P_{ij}) + (∑_j g_j ∑_i P_{ij})
= ⟨f, a⟩ + ⟨g, b⟩`. -/
theorem remark_2_21_weak_duality {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C P : Matrix (Fin n) (Fin m) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b)
    (f : Fin n → ℝ) (g : Fin m → ℝ) (hfg : dualFeasible C f g) :
    ∑ i, ∑ j, P i j * (f i + g j) ≤ ∑ i, ∑ j, P i j * C i j ∧
      ∑ i, ∑ j, P i j * (f i + g j) = (∑ i, f i * ∑ j, P i j) + (∑ j, g j * ∑ i, P i j) ∧
      (∑ i, f i * ∑ j, P i j) + (∑ j, g j * ∑ i, P i j) = dualObj a b f g := by sorry

end CompOT.Duality
