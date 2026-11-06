-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_fderiv_sub_le_of_tendstoCInftyLocOn
-- name    : FiniteEnergyPlane.norm_fderiv_sub_le_of_tendstoCInftyLocOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:48:34.996644+00:00
-- url     : https://prove2.me/theorems/56b8791c-e47c-47d4-99c8-50178c8b4b44
-- title:
--   $C^\infty_{loc}$ convergence gives uniform $C^1$ closeness on compact sets
-- statement:
--   Let $X,Y$ be real normed spaces, $O\subset X$, $K\subset O$ compact, and $f_k\to g$ in $C^\infty_{loc}$ on $O$. Then for every $\varepsilon>0$, for all large $k$, $\|Df_k(x)-Dg(x)\|\le\varepsilon$ for all $x\in K$.
--
--   Role: states the first-derivative part of `JHolomorphic.TendstoCInftyLocOn` in terms of the Frechet derivatives.
-- source:
--   Immediate from the definition of C-infinity-loc convergence

import Definitions.Def_JHolomorphic_Setting

namespace FiniteEnergyPlane

open Filter

/-- If `f k → g` in `C^∞_loc` on `O` and `K ⊆ O` is compact, then for every `ε > 0`, for all large `k`,
`‖D(f k)(x) - Dg(x)‖ ≤ ε` on `K`. -/
theorem norm_fderiv_sub_le_of_tendstoCInftyLocOn {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℕ → X → Y} {g : X → Y}
    {O K : Set X} (hc : JHolomorphic.TendstoCInftyLocOn f g O) (hK : K ⊆ O) (hKc : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ K, ‖fderiv ℝ (f k) x - fderiv ℝ g x‖ ≤ ε := by
  sorry

end FiniteEnergyPlane
