-- Prove2me | Theorems.Thm_BanditCovariates_ABSE_bound_5_3
-- name    : BanditCovariates.ABSE.bound_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:08:06.882415+00:00
-- url     : https://prove2.me/theorems/2dc1743d-c3aa-474d-9b85-e3d2cbb7591f
-- title:
--   (5.3), p. 21 — ℓ_B ≤ C_ℓ|B|^{−2β} logbar(n|B|^{2β+d})
-- statement:
--   Fix $d\ge1$, $0<\beta\le1$, and $L>0$. There is $C_\ell>0$, depending on these parameters only, such that for every $K\ge2$, $n\ge K\log K$, and valid dyadic cell $B$ at depth at most $k_0$,
--
--   $$\ell_B\le C_\ell |B|^{-2\beta}\overline{\log}\!\left(n|B|^{2\beta+d}\right).$$
--
--   This bounds the number of pulls spent in each adaptive cell.
--
--   **Formalization Note** The printed ordinary logarithm can be nonpositive at the finest depth although $\ell_B\ge1$. The modified logarithm follows the radius definition (2.1).
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 21, (5.3); corrected log as in paper.md slip 11

import Mathlib
import Definitions.Def_BanditCovariates_ABSE_Cells

noncomputable section

namespace BanditCovariates.ABSE

/-- Display (5.3), p. 21, with BanditCovariates.SE.logbar at the final dyadic depth. -/
theorem bound_5_3 (d : ℕ) (β L : ℝ)
    (hd : 1 ≤ d) (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K n : ℕ), 2 ≤ K →
      (K : ℝ) * Real.log (K : ℝ) ≤ (n : ℝ) →
      ∀ B : Cell d, ValidCell B → B.depth ≤ k0 d K n β →
        (ell d n β L B : ℝ) ≤
          C * side B ^ (-2 * β) *
            BanditCovariates.SE.logbar ((n : ℝ) * side B ^ (2 * β + (d : ℝ))) := by sorry

end BanditCovariates.ABSE
