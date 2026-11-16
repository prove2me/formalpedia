-- Prove2me | Theorems.Thm_BatchMaxService_Metric_Supplement_blind_phase_cost
-- name    : BatchMaxService.Metric.Supplement.blind_phase_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:07:40.893178+00:00
-- url     : https://prove2.me/theorems/72268c1c-004e-4016-99dd-eea6e1818115
-- title:
--   Lemma 6.1 — Algorithm 5 phase cost is strictly less than 21 times its radius
-- statement:
--   For every completed positive phase $k$ of blind elective Algorithm 5, let $P_k$ be its request identities, $s_{k-1}$ its starting anchor and $s_k$ its endpoint. The request set is nonempty and, writing $R_k$ for its farthest-request distance,
--
--   $$R_k=|s_k-s_{k-1}|=\max_{q\in P_k}|x(q)-s_{k-1}|,\qquad \operatorname{cost}(k)<21R_k.$$
--
--   Phase cost is the sum of the actual exploration and cleanup event bills. Free anchor services have zero cost and are omitted from positive phase records. The strict factor 21 and the endpoint/farthest equality are retained together; the lemma supports Theorem 6.2.
--
--   Differences from the source:
--   - encoding: known finite metrics, distinct requests and real arrival times → enumerated sites Fin n, natural identity labels and unrestricted real arrival times; reason: enumeration preserves every finite metric and repeated location/time pairs; a specified start already excludes the empty carrier
--   - encoding: each positive phase and its request set and actual phase cost → completed operational phase records, their nonempty identity sets and sum of separately billed events; reason: records are created by the controller only at successful cleanup; no cost or endpoint property is a field of a record
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Lemma 6.1, printed p. 21 / PDF p. 22

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Supplement_Blind

namespace BatchMaxService.Metric.Supplement

theorem blind_phase_cost {n : ℕ} [MetricSpace (Fin n)]
    (x : Fin n → ℝ) (hx : IsLine x) (I : RequestInput n) :
    ∀ p ∈ (algorithm5 x I).control.phases,
      p.requests.Nonempty ∧
      |x p.endpoint - x p.anchor| = phaseRadius x I p ∧
      cost I p.events < 21 * phaseRadius x I p := by sorry

end BatchMaxService.Metric.Supplement
