-- Prove2me | Theorems.Thm_AngelDevil_reducedJourney_allowed
-- name    : AngelDevil.reducedJourney_allowed
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:16:24.741931+00:00
-- url     : https://prove2.me/theorems/b6f4b8fc-c1fe-4fc7-a690-ba558187e1e5
-- title:
--   Claim 2.6: allowed journeys remain allowed after reduction
-- statement:
--   For every nonnegative integer power, every Devil strategy and every finite journey allowed against its Nice transformation, the reduced journey is allowed against the original Devil. Allowedness includes both bounded jumps and avoidance of all earlier Devil selections. The statement also covers power zero.
-- source:
--   Andras Mathe, The Angel of power 2 wins, CPC 16 (2007), 363-374; https://doi.org/10.1017/S0963548306008303; author manuscript internal pagination. Claim 2.6, p. 3.

import Definitions.Def_AngelDevil_NiceReduction
open AngelDevil

theorem AngelDevil.reducedJourney_allowed (p : Nat) (D : DevilStrategy) (h : List Point)
    (ha : Allowed p (niceReduction p D) h) : Allowed p D (reducedJourney p h)  := by sorry
