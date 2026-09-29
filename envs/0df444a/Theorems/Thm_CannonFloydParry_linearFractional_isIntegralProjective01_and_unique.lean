-- Prove2me | Theorems.Thm_CannonFloydParry_linearFractional_isIntegralProjective01_and_unique
-- name    : CannonFloydParry.linearFractional_isIntegralProjective01_and_unique
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:09:02.264222+00:00
-- url     : https://prove2.me/theorems/f3c1800d-1b35-4689-8923-68ec5ff4b9cd
-- title:
--   p. 252 — the unique integral projective map between integral subsimplices, by an explicit formula
-- statement:
--   Let $I = [\alpha/\beta, \gamma/\delta]$ and $J = [a/b, c/d]$ satisfy the conditions of p. 251, and let
--   $$f(t) = \frac{(c\beta - a\delta)t + (a\gamma - c\alpha)}{(d\beta - b\delta)t + (b\gamma - d\alpha)}.$$
--   Then $f$ is integral projective on $I$, maps $I$ onto $J$, and sends $\alpha/\beta \mapsto a/b$ and $\gamma/\delta \mapsto c/d$; and every map $g$ integral projective on $I$ that maps $I$ into $J$ with the same endpoint values agrees with $f$ on $I$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, pp. 252–253, integral projective maps for [0,1]

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem linearFractional_isIntegralProjective01_and_unique {I J : FracInterval} (hI : I.IsFarey)
    (hJ : J.IsFarey) :
    let f : ℝ → ℝ := fun t =>
      (((J.c : ℝ) * I.b - (J.a : ℝ) * I.d) * t + ((J.a : ℝ) * I.c - (J.c : ℝ) * I.a)) /
        (((J.d : ℝ) * I.b - (J.b : ℝ) * I.d) * t + ((J.b : ℝ) * I.c - (J.d : ℝ) * I.a))
    IsIntegralProjective01 (Set.Icc I.lo I.hi) f ∧ f '' Set.Icc I.lo I.hi = Set.Icc J.lo J.hi ∧
      f I.lo = J.lo ∧ f I.hi = J.hi ∧
      ∀ g : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) g →
        Set.MapsTo g (Set.Icc I.lo I.hi) (Set.Icc J.lo J.hi) → g I.lo = J.lo → g I.hi = J.hi →
          Set.EqOn g f (Set.Icc I.lo I.hi) := by
  sorry

end CannonFloydParry
