-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_separated_coverage
-- name    : DeletionHash.MixedEdit.separated_coverage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:35.786977+00:00
-- url     : https://prove2.me/theorems/79f1955f-14c9-4530-a5df-bcd6e38c9327
-- title:
--   Lemma 2.7 — separated coverage
-- statement:
--   In the standing proof regime let $x$ be a $k$-unique length-$n$ word. If a valid separated record of exactly $2t$ edits has target $z$ of the same length, then
--   $$R_L(z)-R_L(x)\in K_0.$$
--   The target is computed by applying the record sequentially. Neither a catalogue representation nor target uniqueness is assumed. This supplies the signed-rule coverage conclusion for separated conflicts.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
--   - encoding: a separated record to a same-length target → a computed target and additive boundary p_i+D₀≤n; reason: the additive form is equivalent in the nonnegative boundary regime and avoids truncated subtraction
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 2.7, printed p. 9 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Rules
import Definitions.Def_DeletionHash_MixedEdit_Regime

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 2.7: exactly 2t separated edits, returning to the original length. -/
theorem separated_coverage {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (record : List (Edit α))
    (hvalid : ValidRecord b (letters x) record) (hlen : record.length = 2*t)
    (hsep : Separated n t b L record) (htarget : (target (letters x) record).length = n) :
    spectrum L (target (letters x) record) - spectrum L (letters x) ∈ Catalogue k L t b := by sorry

end DeletionHash.MixedEdit
