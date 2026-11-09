-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_confusable_record
-- name    : DeletionHash.MixedEdit.confusable_record
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:46.77413+00:00
-- url     : https://prove2.me/theorems/f017f64b-0ad7-4347-8307-2af43a528bd7
-- title:
--   Lemma 2.6 — confusable record
-- statement:
--   Let $t\ge2$ and $b\ge1$, and take two distinct words $x,z$ over a finite alphabet of size at least two. If they have a common word reachable from each by at most $t$ bounded substring edits, then
--   $$\exists\text{ valid record from }x\text{ to }z\text{ with at most }2t\text{ edits}.$$
--   Every record entry acts on the word currently present; intermediate and endpoint lengths are unrestricted in this lemma. This supplies the actual short transformation used to analyze a confusable pair.
--
--   Differences from the source:
--   - encoding: a short sequence of actual edits → a list of position/removed-length/replacement records valid on successive words; reason: the source record is represented directly; no distance surrogate is used
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 2.6, printed p. 8 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Channel

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 2.6: arbitrary intermediate lengths, in the actual substring channel. -/
theorem confusable_record {α : Type u} [Fintype α] [DecidableEq α]
    (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) (hq : 2 ≤ Fintype.card α)
    (x z : List α) (hne : x ≠ z) (hconf : Confusable b t x z) :
    ∃ record : List (Edit α), record.length ≤ 2*t ∧ ValidRecord b x record ∧ target x record = z := by sorry

end DeletionHash.MixedEdit
