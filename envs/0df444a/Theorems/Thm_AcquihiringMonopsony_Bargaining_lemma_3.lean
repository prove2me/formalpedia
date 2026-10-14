-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Bargaining_lemma_3
-- name    : AcquihiringMonopsony.Bargaining.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:42.482973+00:00
-- url     : https://prove2.me/theorems/f5e59b64-ddd3-4100-8210-b97057e5da3f
-- title:
--   Lemma 3 — under acquihiring the acquisition occurs if $v_a > v_s + b$, and for $v_a < v_s + b$ exactly when $(1+\delta)v_a > v_s + \delta(b+\underline{w})$
-- statement:
--   Consider the bargaining extension of the acquihiring model with parameters satisfying the standing assumption $b > 0$, $\min\{v_a, v_s\} > b + \underline{w}$, acquirer bargaining power $\alpha \in [0,1]$ and probability $\delta \in [0,1]$ of direct hiring after a failed bid. Suppose the acquirer chooses acquihiring, and let $\sigma_F$ be any continuation equilibrium (in undominated strategies) of the direct-hiring subgame played after a failed bid. Then:
--
--   1. if $v_a > v_s + b$, the acquisition occurs and the employee is hired by the acquirer at the wage $\underline{w}$;
--   2. if $v_a < v_s + b$, no acquisition takes place when $v_s + \delta(b + \underline{w}) > (1+\delta)v_a$; when instead $v_s + \delta(b + \underline{w}) < (1+\delta)v_a$, the acquisition occurs and the employee is hired by the acquirer at the wage $\underline{w}$.
--
--   Lemma 3 is the bargaining counterpart of Lemma 1: it describes the continuation after the acquirer opts for acquihiring, and Proposition 2 compares it with direct hiring.
--
--   **Formalization Note** "The acquirer makes an offer which is accepted" is the event that the Nash-bargaining surplus is positive. The employee's wage $\underline{w}$ after an acquisition is the monopsony wage of the model (as in Lemma 2 of the paper) and is built into the definition of her acquihiring payoff; it is stated here as the paper states it.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 8 (PDF 9), Lemma 3

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model
import Definitions.Def_AcquihiringMonopsony_Bargaining_NashSplit

namespace AcquihiringMonopsony.Bargaining

theorem lemma_3 (P : Baseline.Params) (hP : P.Standing) (α δ : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (σF : Baseline.DHProfile) (hF : Baseline.IsDHEquilibrium P σF) :
    (P.vs + P.b < P.va → AcquisitionOccurs P δ σF ∧ ahPayoffE P δ σF = P.wl) ∧
    (P.va < P.vs + P.b →
      (P.vs + δ * (P.b + P.wl) > (1 + δ) * P.va → ¬ AcquisitionOccurs P δ σF) ∧
      (P.vs + δ * (P.b + P.wl) < (1 + δ) * P.va →
        AcquisitionOccurs P δ σF ∧ ahPayoffE P δ σF = P.wl)) := by sorry

end AcquihiringMonopsony.Bargaining
