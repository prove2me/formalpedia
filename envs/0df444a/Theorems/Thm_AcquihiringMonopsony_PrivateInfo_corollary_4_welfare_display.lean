-- Prove2me | Theorems.Thm_AcquihiringMonopsony_PrivateInfo_corollary_4_welfare_display
-- name    : AcquihiringMonopsony.PrivateInfo.corollary_4_welfare_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:45.39412+00:00
-- url     : https://prove2.me/theorems/b79a6ec3-7a68-47ad-9788-2c3550414974
-- title:
--   Proof of Corollary 4, pp. 17–18 — welfare change from direct hiring to acquihiring, positive iff v_a > v_s + 4B/5
-- statement:
--   In the private-benefit model of §6 ($b \sim U[0,B]$, $0 < B < \min\{v_a,v_s\}$, $v_s - B < v_a < v_s + 2B$), let $b^* = (v_a - v_s + B)/3$ be the type indifferent between the two offers in the direct-hiring equilibrium of Lemma 5. Let $W_{DH}$ be the expected total surplus under direct hiring (types $b < b^*$ produce $v_a$ at the acquirer, types $b \ge b^*$ produce $v_s$ and enjoy $b$ at the startup) and $W_{AH} = v_a$ the surplus when the employee works at the acquirer. Then
--   $$W_{AH} - W_{DH} = \frac{B-b^*}{B}(v_a-v_s) - \frac{B^2-b^{*2}}{2B} = \frac{B-b^*}{2B}\left(2(v_a-v_s) - \frac{v_a-v_s+B}{3} - B\right),$$
--   and this change is strictly positive if and only if $v_a > v_s + 4B/5$, and strictly negative if and only if $v_a < v_s + 4B/5$.
--
--   This display is the computation from which Corollary 4 follows.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), pp. 17–18 (PDF 18–19), proof of Corollary 4, display

import Mathlib
import Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model

namespace AcquihiringMonopsony.PrivateInfo

theorem corollary_4_welfare_display (P : Params) (hP : P.Standing) :
    welfareAH P - welfareDH P =
      (P.B - bStar P) / P.B * (P.va - P.vs) - (P.B ^ 2 - bStar P ^ 2) / (2 * P.B) ∧
    (P.B - bStar P) / P.B * (P.va - P.vs) - (P.B ^ 2 - bStar P ^ 2) / (2 * P.B) =
      (P.B - bStar P) / (2 * P.B) * (2 * (P.va - P.vs) - (P.va - P.vs + P.B) / 3 - P.B) ∧
    (0 < welfareAH P - welfareDH P ↔ P.vs + 4 * P.B / 5 < P.va) ∧
    (welfareAH P - welfareDH P < 0 ↔ P.va < P.vs + 4 * P.B / 5) := by sorry

end AcquihiringMonopsony.PrivateInfo
