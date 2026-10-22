-- Prove2me | Theorems.Thm_AcquihiringMonopsony_PrivateInfo_profit_comparison_roots
-- name    : AcquihiringMonopsony.PrivateInfo.profit_comparison_roots
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:53.476922+00:00
-- url     : https://prove2.me/theorems/5dea59c0-a135-44a7-bd07-1c4670133b23
-- title:
--   Proof of Proposition 5, p. 17 — the profits are equal at v̂_a and v_s + (7+3√5)B/2; acquihiring wins in between
-- statement:
--   Let $B > 0$ and write $\hat v_a = v_s + \frac{7-3\sqrt5}{2}B$ and $\check v_a = v_s + \frac{7+3\sqrt5}{2}B$. Compare the acquirer's profit under acquihiring, $v_a - v_s$, with its direct-hiring profit $\frac{(v_a-v_s+B)^2}{9B}$ from Lemma 5. Then
--   $$\frac{(v_a-v_s+B)^2}{9B} < v_a - v_s \iff \hat v_a < v_a < \check v_a ,$$
--   the two profits are equal exactly when $v_a = \hat v_a$ or $v_a = \check v_a$, and
--   $$v_s + 2B < \check v_a ,$$
--   so the upper root lies outside the range $v_a < v_s + 2B$ allowed in §6.
--
--   This is the computation behind Proposition 5: within the parameter range of §6 only the lower root $\hat v_a$ matters.
--
--   **Formalization Note** Only $B > 0$ is assumed; the statement is pure algebra in $(v_a - v_s)/B$ and holds without the remaining standing assumptions.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 17 (PDF 18), proof of Proposition 5, first paragraph

import Mathlib
import Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model

namespace AcquihiringMonopsony.PrivateInfo

theorem profit_comparison_roots (P : Params) (hB : 0 < P.B) :
    ((P.va - P.vs + P.B) ^ 2 / (9 * P.B) < P.va - P.vs ↔
      vHat P < P.va ∧ P.va < P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B) ∧
    ((P.va - P.vs + P.B) ^ 2 / (9 * P.B) = P.va - P.vs ↔
      P.va = vHat P ∨ P.va = P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B) ∧
    P.vs + 2 * P.B < P.vs + (7 + 3 * Real.sqrt 5) / 2 * P.B := by sorry

end AcquihiringMonopsony.PrivateInfo
