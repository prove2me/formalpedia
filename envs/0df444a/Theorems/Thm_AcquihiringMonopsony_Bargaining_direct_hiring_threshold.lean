-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Bargaining_direct_hiring_threshold
-- name    : AcquihiringMonopsony.Bargaining.direct_hiring_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:43.070982+00:00
-- url     : https://prove2.me/theorems/e0e790ee-6b7a-4c8f-bdaa-59253ff944c3
-- title:
--   Proof of Proposition 2, p. 9 — for $v_a \ge v_s + b$, direct hiring pays more than acquihiring iff $v_a > \overline{v}_a$
-- statement:
--   Consider the bargaining extension of the acquihiring model with parameters satisfying the standing assumption $b > 0$, $\min\{v_a, v_s\} > b + \underline{w}$, acquirer bargaining power $\alpha \in (0,1)$ and probability $\delta \in (0,1)$ of direct hiring after a failed bid. Let $\sigma_D$ be any continuation equilibrium (in undominated strategies) of the direct-hiring subgame chosen at the first stage, and $\sigma_F$ any continuation equilibrium of the direct-hiring subgame played after a failed bid. If $v_a \ge v_s + b$, then the acquirer's direct-hiring payoff exceeds its acquihiring payoff if and only if
--
--   $$v_a > \overline{v}_a = v_s + b + \frac{\alpha}{(1-\alpha)(1-\delta)}\bigl[\delta(v_s - \underline{w}) + b\bigr].$$
--
--   This comparison is the first step of the proof of Proposition 2 and is where the upper threshold $\overline{v}_a$ comes from.
--
--   **Formalization Note** The case includes the knife-edge $v_a = v_s + b$, as on the page. Lemma 1 and Lemma 3 are stated for strict inequalities only; at the knife-edge every direct-hiring equilibrium gives both firms payoff $0$, so the acquihiring payoff formula of the case $v_a > v_s + b$ still applies. The ranges $0 < \alpha < 1$, $0 < \delta < 1$ are those of Proposition 2 as formalized in this mission (see the goal theorem).
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 9 (PDF 10), proof of Proposition 2, first paragraph

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model
import Definitions.Def_AcquihiringMonopsony_Bargaining_NashSplit

namespace AcquihiringMonopsony.Bargaining

theorem direct_hiring_threshold (P : Baseline.Params) (hP : P.Standing) (α δ : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (σD σF : Baseline.DHProfile) (hD : Baseline.IsDHEquilibrium P σD)
    (hF : Baseline.IsDHEquilibrium P σF) (hva : P.vs + P.b ≤ P.va) :
    ahPayoffA P α δ σF < Baseline.dhPayoffA P σD.acceptA σD.wa σD.ws ↔ vUpper P α δ < P.va := by sorry

end AcquihiringMonopsony.Bargaining
