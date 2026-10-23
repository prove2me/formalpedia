-- Prove2me | Theorems.Thm_CircletTSP_Facet_stsp_dim
-- name    : CircletTSP.Facet.stsp_dim
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:12.722606+00:00
-- url     : https://prove2.me/theorems/7c3dc193-fa26-4ae5-9c21-3691a8e4c62e
-- title:
--   p. 19 (Naddef–Rinaldi, Theorem 3.7) — dim STSP(n) = |E| − |V| = n(n − 3)/2
-- statement:
--   For $n\ge 3$, the symmetric traveling salesman polytope has dimension
--   $$\dim STSP(n)=|E|-|V|=\frac{n(n-3)}{2}.$$
--
--   The paper cites this from Naddef and Rinaldi (Theorem 3.7) to reduce the facet property of a valid inequality to exhibiting $n(n-3)/2$ tight Hamiltonian cycles with linearly independent incidence vectors.
--
--   **Formalization Note** The dimension is that of the affine hull (`Disjunctive.Polarity.PolyDim`, the finrank of the vector span). $STSP(n)$ sits in ordered-pair coordinates `Fin n → Fin n → ℝ`; the embedding of $\mathbb R^E$ as symmetric zero-diagonal arrays is linear and injective, so the dimension is the one in $\mathbb R^E$. This is a cited classical result, not a theorem of the paper, and is stated for all $n\ge 3$.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 19, citing Naddef and Rinaldi [28], Theorem 3.7

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- The dimension of the symmetric TSP polytope (p. 19, cited from Naddef and Rinaldi,
Theorem 3.7): for `n ≥ 3`, `dim STSP(n) = |E| - |V| = n(n - 3)/2`. -/
theorem stsp_dim (n : ℕ) (hn : 3 ≤ n) :
    Disjunctive.Polarity.PolyDim (STSP n) = ((n * (n - 3) / 2 : ℕ) : ℤ) := by sorry

end CircletTSP.Facet
