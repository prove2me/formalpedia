-- Prove2me | Theorems.Thm_CannonFloydParry_isPLFSlopeOne_extend
-- name    : CannonFloydParry.isPLFSlopeOne_extend
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-15T19:26:18.810263+00:00
-- url     : https://prove2.me/theorems/34e690ab-5980-4e3f-a201-eb7cefa9b2ec
-- title:
--   $F$ lies in the slope-one group of the line
-- statement:
--   Let $f$ be an element of Thompson's group $F$, and extend it by the identity to a map of
--   the whole real line. Then that extension is an orientation-preserving piecewise-linear
--   homeomorphism of $\mathbb{R}$ with finitely many breakpoints which has slope $1$ near $-\infty$
--   and near $+\infty$.
--
--   This is exactly the supergroup of $F$ that Cannon-Floyd-Parry name when they attribute Theorem
--   4.8 and Corollary 4.9 to Brin and Squier, and it is the bridge along which the Brin-Squier
--   theorem is imported into this mission.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathematique (2) 42 (1996) 215-256, https://doi.org/10.5169/seals-87877, section 4, p. 231, the remark following Corollary 4.7

import Definitions.Def_CannonFloydParry
import Definitions.Def_BrinSquier
import Mathlib

namespace CannonFloydParry

theorem isPLFSlopeOne_extend {f : UI ≃o UI} (hf : f ∈ F) :
    BrinSquier.IsPLFSlopeOne (extend f) := by
  sorry

end CannonFloydParry
