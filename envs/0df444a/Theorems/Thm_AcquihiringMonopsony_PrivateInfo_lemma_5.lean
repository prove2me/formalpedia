-- Prove2me | Theorems.Thm_AcquihiringMonopsony_PrivateInfo_lemma_5
-- name    : AcquihiringMonopsony.PrivateInfo.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:42.61498+00:00
-- url     : https://prove2.me/theorems/e89e3f8b-dab4-448b-8cfa-4f52bd49aa0a
-- title:
--   Lemma 5 — direct-hiring equilibrium wages (2v_a+v_s−B)/3, (2v_s+v_a−2B)/3, poaching probability, profit (v_a−v_s+B)²/(9B)
-- statement:
--   In the private-benefit model of §6 ($b \sim U[0,B]$, outside option $0$, $0 < B < \min\{v_a,v_s\}$ and $v_s - B < v_a < v_s + 2B$), suppose the acquirer chooses direct hiring, and let
--   $$w_a^* = \frac{2v_a + v_s - B}{3}, \qquad w_s^* = \frac{2v_s + v_a - 2B}{3}.$$
--   Then:
--
--   1. $(w_a^*, w_s^*)$ is an equilibrium of the wage game: $w_a^*$ maximizes the acquirer's expected profit given $w_s^*$, and $w_s^*$ maximizes the startup's given $w_a^*$, each over all real wages;
--   2. $w_a^* > 0$ and $w_s^* > 0$;
--   3. the probability that the acquirer's offer is accepted is
--   $$0 < \frac{v_a - v_s + B}{3B} < 1 ;$$
--   4. the acquirer's expected profit is $\dfrac{(v_a-v_s+B)^2}{9B}$;
--   5. any equilibrium $(w_a,w_s)$ with $w_a \ge 0$ and $0 < w_a - w_s < B$ (the region where the page's first-order conditions apply) equals $(w_a^*,w_s^*)$.
--
--   This is the continuation equilibrium under direct hiring that Proposition 5 compares with acquihiring.
--
--   **Formalization Note** The page derives the wages from first-order conditions in the interior region $w_a \ge 0$, $0 < w_a - w_s < B$. Clause 1 claims global best responses over all real wages, which is stronger than the first-order conditions; uniqueness is claimed only within the interior region, because the page does not show uniqueness among all equilibria.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 16 (PDF 17), Lemma 5 and its proof

import Mathlib
import Definitions.Def_AcquihiringMonopsony_PrivateInfo_Model

namespace AcquihiringMonopsony.PrivateInfo

theorem lemma_5 (P : Params) (hP : P.Standing) :
    IsDHEquilibrium P (waStar P) (wsStar P) ∧
    0 < waStar P ∧ 0 < wsStar P ∧
    poachProb P (waStar P) (wsStar P) = (P.va - P.vs + P.B) / (3 * P.B) ∧
    0 < (P.va - P.vs + P.B) / (3 * P.B) ∧ (P.va - P.vs + P.B) / (3 * P.B) < 1 ∧
    profitA P (waStar P) (wsStar P) = (P.va - P.vs + P.B) ^ 2 / (9 * P.B) ∧
    (∀ wa ws : ℝ, IsDHEquilibrium P wa ws → 0 ≤ wa → 0 < wa - ws → wa - ws < P.B →
      wa = waStar P ∧ ws = wsStar P) := by sorry

end AcquihiringMonopsony.PrivateInfo
