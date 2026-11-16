-- Prove2me | Theorems.Thm_BatchMaxService_Metric_Supplement_offline_service_equivalence
-- name    : BatchMaxService.Metric.Supplement.offline_service_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:03:56.546004+00:00
-- url     : https://prove2.me/theorems/791387c7-a794-44fc-932c-a632cdc8f2ab
-- title:
--   Theorem 3.2 — Automatic and elective offline infima coincide
-- statement:
--   For every finite input $I$ on a known finite metric, with instantaneous movement, complete epochs before same-time actions and the common unit waiting rate,
--
--   $$\operatorname{OPT}_{\rm auto}(I)=\operatorname{OPT}_{\rm elective}(I).$$
--
--   Both values are infima over all feasible schedules for their own service rule, using the same start and the same movement plus per-batch maximum delay objective. Automatic batches need not be consecutive arrival blocks. This equality supplies the offline comparator for the automatic companion results.
--
--   Differences from the source:
--   - encoding: known finite metrics, distinct requests and real arrival times → enumerated sites Fin n, natural identity labels and unrestricted real arrival times; reason: enumeration preserves every finite metric and repeated location/time pairs; a specified start already excludes the empty carrier
--   - encoding: offline infimum of nonnegative schedule costs → ENNReal infima over the unrestricted feasible-schedule subtypes; reason: empty indexing yields positive infinity instead of a default real zero; no competitor is omitted
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Theorem 3.2, printed p. 6 / PDF p. 7

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Supplement_Automatic

namespace BatchMaxService.Metric.Supplement

theorem offline_service_equivalence {n : ℕ} [MetricSpace (Fin n)]
    (I : RequestInput n) : OPTauto I = OPT I := by sorry

end BatchMaxService.Metric.Supplement
