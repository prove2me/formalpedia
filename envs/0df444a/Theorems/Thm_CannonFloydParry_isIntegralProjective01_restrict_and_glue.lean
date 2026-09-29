-- Prove2me | Theorems.Thm_CannonFloydParry_isIntegralProjective01_restrict_and_glue
-- name    : CannonFloydParry.isIntegralProjective01_restrict_and_glue
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:09:30.514323+00:00
-- url     : https://prove2.me/theorems/98873d26-b434-4ed4-a8a4-f02d2d0ea840
-- title:
--   p. 253 — integral projective maps restrict to, and are glued from, maps of the left and right parts
-- statement:
--   Let $I$ and $J$ satisfy the conditions of p. 251. (i) If $f$ is integral projective on $I$ and sends the endpoints of $I$ to those of $J$, then $f$ sends the mediant of $I$ to the mediant of $J$, and maps the left part of $I$ onto the left part of $J$ and the right part onto the right part. (ii) If $g_1$ is integral projective on the left part of $I$ and sends its endpoints to those of the left part of $J$, and $g_2$ does the same for the right parts, then some $g$ integral projective on $I$ agrees with $g_1$ on the left part and with $g_2$ on the right part.
--
--   **Formalization Note.** The endpoint conditions in (ii) are not in the source's converse. Without them it fails: maps of the halves that each exchange the endpoints are integral projective but do not glue to one map of $I$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 253, integral projective maps for [0,1]

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem isIntegralProjective01_restrict_and_glue {I J : FracInterval} (hI : I.IsFarey)
    (hJ : J.IsFarey) :
    (∀ f : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) f → f I.lo = J.lo → f I.hi = J.hi →
        f I.rightPart.lo = J.rightPart.lo ∧
          f '' Set.Icc I.leftPart.lo I.leftPart.hi = Set.Icc J.leftPart.lo J.leftPart.hi ∧
          f '' Set.Icc I.rightPart.lo I.rightPart.hi = Set.Icc J.rightPart.lo J.rightPart.hi) ∧
      ∀ g₁ g₂ : ℝ → ℝ,
        IsIntegralProjective01 (Set.Icc I.leftPart.lo I.leftPart.hi) g₁ →
        g₁ I.leftPart.lo = J.leftPart.lo → g₁ I.leftPart.hi = J.leftPart.hi →
        IsIntegralProjective01 (Set.Icc I.rightPart.lo I.rightPart.hi) g₂ →
        g₂ I.rightPart.lo = J.rightPart.lo → g₂ I.rightPart.hi = J.rightPart.hi →
        ∃ g : ℝ → ℝ, IsIntegralProjective01 (Set.Icc I.lo I.hi) g ∧
          Set.EqOn g g₁ (Set.Icc I.leftPart.lo I.leftPart.hi) ∧
          Set.EqOn g g₂ (Set.Icc I.rightPart.lo I.rightPart.hi) := by
  sorry

end CannonFloydParry
