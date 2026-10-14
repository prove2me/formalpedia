-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Bargaining_threat_points_low
-- name    : AcquihiringMonopsony.Bargaining.threat_points_low
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:53.78614+00:00
-- url     : https://prove2.me/theorems/928ce48a-39dd-4890-a6c2-6cab54aa74e2
-- title:
--   Proof of Lemma 3, p. 8 — if $v_a < v_s + b$: $t_a = 0$, $t_s$, acquisition iff $(1+\delta)v_a > v_s + \delta(b + \underline{w})$, acquirer's payoff
-- statement:
--   Consider the bargaining extension of the acquihiring model with parameters satisfying the standing assumption $b > 0$, $\min\{v_a, v_s\} > b + \underline{w}$, acquirer bargaining power $\alpha \in [0,1]$ and probability $\delta \in [0,1]$ of direct hiring after a failed bid. Let $\sigma_F$ be any continuation equilibrium (in undominated strategies) of the direct-hiring subgame played after a failed bid. If $v_a < v_s + b$, then
--
--   $$t_a = 0, \qquad t_s = (1-\delta)(v_s - \underline{w}) + \delta\bigl[v_s - (v_a - b)\bigr],$$
--
--   the acquisition occurs if and only if
--
--   $$(1+\delta)\,v_a > v_s + \delta(b + \underline{w}),$$
--
--   and when it occurs the acquirer's payoff from acquihiring is
--
--   $$v_a - \underline{w} - p = \alpha\bigl[(1+\delta)v_a - v_s - \delta(b + \underline{w})\bigr].$$
--
--   This is the second case of the proof of Lemma 3; it determines the lower threshold $\underline{v}_a$ of Proposition 2.
--
--   **Formalization Note** The paper's last display of this case reads $-\delta(b - \underline{w})$; recomputing from the price formula on the line above ($p = \alpha v_s + (1-\alpha-\alpha\delta)v_a + \delta\alpha b - (1-\alpha\delta)\underline{w}$) gives $-\delta(b + \underline{w})$, which is what is stated here.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 8 (PDF 9), proof of Lemma 3, second paragraph (case v_a < v_s + b); last display corrected from −δ(b − w̲) to −δ(b + w̲)

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model
import Definitions.Def_AcquihiringMonopsony_Bargaining_NashSplit

namespace AcquihiringMonopsony.Bargaining

theorem threat_points_low (P : Baseline.Params) (hP : P.Standing) (α δ : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (σF : Baseline.DHProfile) (hF : Baseline.IsDHEquilibrium P σF)
    (hva : P.va < P.vs + P.b) :
    threatA P δ σF = 0 ∧
    threatS P δ σF = (1 - δ) * (P.vs - P.wl) + δ * (P.vs - (P.va - P.b)) ∧
    (AcquisitionOccurs P δ σF ↔ P.vs + δ * (P.b + P.wl) < (1 + δ) * P.va) ∧
    (AcquisitionOccurs P δ σF →
      ahPayoffA P α δ σF = α * ((1 + δ) * P.va - P.vs - δ * (P.b + P.wl))) := by sorry

end AcquihiringMonopsony.Bargaining
