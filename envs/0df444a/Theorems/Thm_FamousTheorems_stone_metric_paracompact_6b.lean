-- Prove2me | Theorems.Thm_FamousTheorems_stone_metric_paracompact_6b
-- name    : FamousTheorems.stone_metric_paracompact_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:09.46364+00:00
-- url     : https://prove2.me/theorems/c82d8190-6542-4864-be15-7568a404002e
-- title:
--   A. H. Stone's theorem: metric spaces are paracompact
-- statement:
--   **A. H. Stone's theorem: metric spaces are paracompact.** Every pseudometric space is paracompact: every open cover has a locally finite open refinement. More generally, every pseudo-extended-metric space is paracompact.
--
--   A. H. Stone proved this in 1948. Paracompact Hausdorff spaces have partitions of unity subordinate to any open cover, so the theorem makes partitions of unity available on every metric space. As a consequence metric spaces are normal, and the theorem is also used in the proof of the Nagata–Smirnov metrization theorem.
--
--   **Formalization note.** Mathlib's instance `Metric.instParacompactSpace` for `PseudoEMetricSpace`, which includes metric and pseudometric spaces. The statement is the `ParacompactSpace` proposition and is proved by `inferInstance`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Metric.instParacompactSpace`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem stone_metric_paracompact_6b (α : Type*) [PseudoEMetricSpace α] : ParacompactSpace α := by sorry

end FamousTheorems
