-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_sub_lt_of_tendstoCInftyLocOn
-- name    : FiniteEnergyPlane.norm_sub_lt_of_tendstoCInftyLocOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:45:53.900217+00:00
-- url     : https://prove2.me/theorems/ed035bda-88aa-46ee-9263-02cf2664c9f7
-- title:
--   $C^\infty_{loc}$ convergence gives uniform $C^0$ closeness on compact sets
-- statement:
--   Let $X,Y$ be real normed spaces, $O\subset X$, $K\subset O$ compact, and $f_k\to g$ in $C^\infty_{loc}$ on $O$. Then for every $\varepsilon>0$, for all large $k$, $\|f_k(x)-g(x)\|<\varepsilon$ for all $x\in K$.
--
--   Role: states the $C^0$ part of `JHolomorphic.TendstoCInftyLocOn` in terms of $f_k$ and $g$ themselves.
-- source:
--   Immediate from the definition of C-infinity-loc convergence

import Definitions.Def_JHolomorphic_Setting

namespace FiniteEnergyPlane

open Filter

/-- If `f k → g` in `C^∞_loc` on `O` and `K ⊆ O` is compact, then for every `ε > 0`, for all large `k`,
`‖f k x - g x‖ < ε` on `K`. -/
theorem norm_sub_lt_of_tendstoCInftyLocOn {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℕ → X → Y} {g : X → Y} {O K : Set X}
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) (hK : K ⊆ O) (hKc : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in atTop, ∀ x ∈ K, ‖f k x - g x‖ < ε := by
  sorry

end FiniteEnergyPlane
