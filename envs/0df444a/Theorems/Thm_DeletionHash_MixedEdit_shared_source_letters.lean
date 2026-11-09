-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_shared_source_letters
-- name    : DeletionHash.MixedEdit.shared_source_letters
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:13.091589+00:00
-- url     : https://prove2.me/theorems/e7136390-9b97-4a7c-8d21-63d483e92122
-- title:
--   Lemma 2.3 — shared source letters
-- statement:
--   In the standing proof regime, let $x\in W_{n,k}$ and choose two valid derivations from $x$, each consisting of zero or one edit. Call their targets $y,z$, and mark replacement letters as new and all retained letters by their original source indices. If valid length-$m$ windows, $m=L-1$, at starts $i,j$ spell the same word, then there is an offset $o$ with $o+k\le m$ such that
--   $$\text{for every }0\le h<k,\ y_{i+o+h}\text{ and }z_{j+o+h}\text{ are original with the same source index}.$$
--   Consequently every word obtained from $x$ by at most one edit is $m$-unique. The trace is computed from the chosen edits, retaining the source-position conclusion rather than only equality of letters.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
--   - encoding: original letters with source positions in a chosen derivation → a computed list of optional source indices and explicit valid-window bounds; reason: none marks a new letter; list access is checked through Option rather than an out-of-range default
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 2.3, printed p. 6 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_SourceTrace
import Definitions.Def_DeletionHash_MixedEdit_Regime

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 2.3, including the m-uniqueness consequence for every one-edit derivation. -/
theorem shared_source_letters {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) :
    (∀ e f : Option (Edit α), ValidOne b (letters x) e → ValidOne b (letters x) f →
      ∀ i j : ℕ, i+(L-1) ≤ (oneWord (letters x) e).length →
        j+(L-1) ≤ (oneWord (letters x) f).length →
        window (L-1) (oneWord (letters x) e) i = window (L-1) (oneWord (letters x) f) j →
        ∃ o : ℕ, o+k ≤ L-1 ∧ ∀ h : ℕ, h < k → ∃ s : ℕ,
          (sourceTrace (letters x) e)[i+o+h]? = some (some s) ∧
          (sourceTrace (letters x) f)[j+o+h]? = some (some s)) ∧
    (∀ e : Option (Edit α), ValidOne b (letters x) e → IsUnique (L-1) (oneWord (letters x) e)) := by sorry

end DeletionHash.MixedEdit
