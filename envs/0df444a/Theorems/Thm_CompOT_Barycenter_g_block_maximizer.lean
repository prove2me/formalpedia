-- Prove2me | Theorems.Thm_CompOT_Barycenter_g_block_maximizer
-- name    : CompOT.Barycenter.g_block_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:38.163126+00:00
-- url     : https://prove2.me/theorems/364d445e-5819-4aa1-81cf-d398a28f199e
-- title:
--   (9.18), pp. 530–531 — column-potential block maximizer
-- statement:
--   Fix a nonempty barycenter support, a cost matrix $C$, a positive regularization parameter $\varepsilon$, a strictly positive target histogram $b$, and a row potential $f$. Put $K_{ij}=e^{-C_{ij}/\varepsilon}$ and $u_i=e^{f_i/\varepsilon}$. In the dual objective, the column potential $g$ maximizes its block when
--   $$g_j=\varepsilon\log\frac{b_j}{\sum_iK_{ij}u_i},\qquad e^{g_j/\varepsilon}=\frac{b_j}{\sum_iK_{ij}u_i}.$$
--   This $g$ gives at least as large a block objective as any other column potential.
--
--   The identity is the dual interpretation of the column-scaling update in (9.18).
--
--   **Formalization Note** The page says “minimizing (9.21)” although (9.21) is displayed as a maximum. The theorem uses maximization. Positive $b_j$ permits the logarithm, and the nonempty row index makes its denominator positive.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (9.18), p. 529; paragraph after proof of Proposition 9.1, pp. 530–531

import Mathlib
import Definitions.Def_CompOT_Barycenter_Defs

namespace CompOT.Barycenter

/-- The column-potential block optimum is the scaling update (9.18),
as stated after Proposition 9.1 on pp. 530–531. -/
theorem g_block_maximizer {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (C : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin m → ℝ) (hbSimplex : b ∈ stdSimplex ℝ (Fin m))
    (hb : ∀ j, 0 < b j) (f : Fin n → ℝ) :
    (∀ g : Fin m → ℝ,
      gBlockObjective ε C b f g ≤
        gBlockObjective ε C b f (gBlockUpdate ε C b f)) ∧
    (∀ j, Real.exp (gBlockUpdate ε C b f j / ε) =
      b j / (∑ i, gibbs ε C i j * Real.exp (f i / ε))) := by sorry

end CompOT.Barycenter
