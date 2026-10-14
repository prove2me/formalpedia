-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Bargaining_threat_points_high
-- name    : AcquihiringMonopsony.Bargaining.threat_points_high
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:44.226087+00:00
-- url     : https://prove2.me/theorems/6e21e39c-5e73-4cfc-9fcf-c2e5fd24fedd
-- title:
--   Proof of Lemma 3, p. 8 — if $v_a > v_s + b$: $t_a = \delta[v_a-(v_s+b)]$, $t_s = (1-\delta)(v_s-\underline{w})$, acquisition occurs, acquirer's payoff
-- statement:
--   Consider the bargaining extension of the acquihiring model with parameters satisfying the standing assumption $b > 0$, $\min\{v_a, v_s\} > b + \underline{w}$, acquirer bargaining power $\alpha \in [0,1]$ and probability $\delta \in [0,1]$ of direct hiring after a failed bid. Let $\sigma_F$ be any continuation equilibrium (in undominated strategies) of the direct-hiring subgame played after a failed bid. If $v_a > v_s + b$, then the threat points are
--
--   $$t_a = \delta\bigl[v_a - (v_s + b)\bigr], \qquad t_s = (1-\delta)(v_s - \underline{w}),$$
--
--   the surplus $v_a - \underline{w} - (t_a + t_s)$ is positive, so the acquisition occurs, and the acquirer's payoff from acquihiring is
--
--   $$v_a - \underline{w} - p = [\alpha(1-\delta) + \delta]\,v_a - \alpha\delta\,\underline{w} - [\alpha(1-2\delta) + \delta]\,v_s - (1-\alpha)\delta\, b.$$
--
--   This is the first case of the proof of Lemma 3. It combines Lemma 1 (the outcome of direct hiring when $v_a > v_s + b$) with the Nash split, and it supplies the acquihiring payoff that the proof of Proposition 2 compares with direct hiring.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 8 (PDF 9), proof of Lemma 3, first paragraph (case v_a > v_s + b)

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model
import Definitions.Def_AcquihiringMonopsony_Bargaining_NashSplit

namespace AcquihiringMonopsony.Bargaining

theorem threat_points_high (P : Baseline.Params) (hP : P.Standing) (α δ : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (σF : Baseline.DHProfile) (hF : Baseline.IsDHEquilibrium P σF)
    (hva : P.vs + P.b < P.va) :
    threatA P δ σF = δ * (P.va - (P.vs + P.b)) ∧
    threatS P δ σF = (1 - δ) * (P.vs - P.wl) ∧
    AcquisitionOccurs P δ σF ∧
    ahPayoffA P α δ σF = (α * (1 - δ) + δ) * P.va - α * δ * P.wl
      - (α * (1 - 2 * δ) + δ) * P.vs - (1 - α) * δ * P.b := by sorry

end AcquihiringMonopsony.Bargaining
