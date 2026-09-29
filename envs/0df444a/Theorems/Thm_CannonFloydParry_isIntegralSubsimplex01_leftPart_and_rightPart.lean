-- Prove2me | Theorems.Thm_CannonFloydParry_isIntegralSubsimplex01_leftPart_and_rightPart
-- name    : CannonFloydParry.isIntegralSubsimplex01_leftPart_and_rightPart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T20:08:06.388857+00:00
-- url     : https://prove2.me/theorems/4f5df7af-68af-495c-8b5f-803ce67dde01
-- title:
--   p. 251 — the left and right parts of an integral subsimplex are integral
-- statement:
--   If $[a/b, c/d]$ satisfies the conditions of p. 251 ($b, c, d > 0$, $a \le b$, $c \le d$, $ad - bc = -1$), then its left part $[a/b, (a+c)/(b+d)]$ and right part $[(a+c)/(b+d), c/d]$ are integral subsimplices of $[0,1]$.
--
--   **Formalization Note.** The source's hypothesis is "$a, b, c, d$ are as above such that $[a/b, c/d]$ is an integral subsimplex"; by the previous milestone this is $ad - bc = -1$, which is what the parts are computed from ($[0/2, 1/1]$ is integral but its right part $[1/3, 1]$ is not).
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 7, p. 251, integral subsimplices of [0,1]

import Mathlib
import Definitions.Def_CannonFloydParry_PIP

namespace CannonFloydParry

theorem isIntegralSubsimplex01_leftPart_and_rightPart {I : FracInterval} (hI : I.IsFarey) :
    IsIntegralSubsimplex01 I.leftPart.lo I.leftPart.hi ∧
      IsIntegralSubsimplex01 I.rightPart.lo I.rightPart.hi := by
  sorry

end CannonFloydParry
