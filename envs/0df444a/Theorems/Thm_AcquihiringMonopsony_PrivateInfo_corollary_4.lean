-- Prove2me | Theorems.Thm_AcquihiringMonopsony_PrivateInfo_corollary_4
-- name    : AcquihiringMonopsony.PrivateInfo.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:54.999615+00:00
-- url     : https://prove2.me/theorems/dfbf62fe-29d9-4882-b1b4-b3ed8782b2f3
-- title:
--   Corollary 4 — acquihiring is more efficient iff v_a > v_s + (4/5)B; chosen direct hiring is efficient, chosen acquihiring may not be
-- statement:
--   In the private-benefit model of §6 ($b \sim U[0,B]$, $0 < B < \min\{v_a,v_s\}$, $v_s - B < v_a < v_s + 2B$), let $W_{DH}$ be expected total surplus under direct hiring at Lemma 5's equilibrium wages and $W_{AH} = v_a$ the surplus with the employee at the acquirer. Let $\hat v_a = v_s + \frac{7-3\sqrt5}{2}B$. Then:
--
--   1. if $v_a > v_s + \frac45 B$, then $W_{AH} > W_{DH}$ (acquihiring is more efficient);
--   2. if $v_a < v_s + \frac45 B$, then $W_{DH} > W_{AH}$ (direct hiring is more efficient);
--   3. whenever direct hiring occurs ($v_a < \hat v_a$), it is more efficient: $W_{DH} > W_{AH}$;
--   4. if
--   $$\frac{7-3\sqrt5}{2} < \frac{v_a - v_s}{B} < \frac45,$$
--   the acquirer's direct-hiring profit is strictly below its acquihiring profit $\max\{0, v_a - v_s\}$ (acquihiring occurs in equilibrium) and yet $W_{DH} > W_{AH}$.
--
--   Together with Proposition 5, this says that equilibrium acquihiring can be socially excessive while equilibrium direct hiring never is.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 17 (PDF 18), Corollary 4

import Mathlib
import Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model

namespace AcquihiringMonopsony.PrivateInfo

theorem corollary_4 (P : Params) (hP : P.Standing) :
    (P.vs + 4 / 5 * P.B < P.va → welfareDH P < welfareAH P) ∧
    (P.va < P.vs + 4 / 5 * P.B → welfareAH P < welfareDH P) ∧
    (P.va < vHat P → welfareAH P < welfareDH P) ∧
    ((7 - 3 * Real.sqrt 5) / 2 < (P.va - P.vs) / P.B → (P.va - P.vs) / P.B < 4 / 5 →
      profitA P (waStar P) (wsStar P) < ahProfitA P ∧ welfareAH P < welfareDH P) := by sorry

end AcquihiringMonopsony.PrivateInfo
