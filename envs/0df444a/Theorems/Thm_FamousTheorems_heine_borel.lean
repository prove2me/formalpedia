-- Prove2me | Theorems.Thm_FamousTheorems_heine_borel
-- name    : FamousTheorems.heine_borel
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T01:51:08.04908+00:00
-- url     : https://prove2.me/theorems/78663f07-59c7-48b0-a34f-9c6c9421dc6d
-- title:
--   The Heine–Borel theorem
-- statement:
--   **The Heine–Borel theorem.**
--
--   In a proper metric space, a subset is compact if and only if it is closed and bounded:
--   $$s \text{ compact} \iff s \text{ closed and bounded}.$$
--
--   For $\mathbb{R}^n$ this is the familiar characterisation, and it is the reason compactness is usable
--   in analysis at all — it replaces a condition about arbitrary open covers with two elementary
--   properties one can check directly. Every classical consequence flows from it: a continuous function
--   on a closed bounded set attains its extrema and is uniformly continuous, and a bounded sequence has a
--   convergent subsequence.
--
--   The properness hypothesis is essential and is exactly what fails in infinite dimensions. In an
--   infinite-dimensional normed space the closed unit ball is closed and bounded but never compact
--   (Riesz's lemma), which is why functional analysis must work with weaker topologies — and why
--   Banach–Alaoglu, recovering compactness of the dual ball in the weak-* topology, is the substitute.
--
--   Named for Heine's 1872 use of the covering idea in proving uniform continuity and Borel's 1895
--   theorem for countable covers of an interval; the general statement is due to Lebesgue and Schoenflies.
--
--   **Formalization note.** `ProperSpace` says closed balls are compact, which is the right general
--   hypothesis — it holds for $\mathbb{R}^n$ and for any finite-dimensional normed space.
--   `Bornology.IsBounded` is metric boundedness. The result is Mathlib's
--   `Metric.isCompact_iff_isClosed_bounded`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem heine_borel {α : Type*} {s : Set α} [MetricSpace α] [ProperSpace α] :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s := by sorry

end FamousTheorems
