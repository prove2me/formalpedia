-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_connected_blocks
-- name    : DeletionHash.MixedEdit.connected_blocks
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:59.949449+00:00
-- url     : https://prove2.me/theorems/a4a22a81-1846-4ad6-af36-d04146d0e1a4
-- title:
--   Lemma 4.5 — connected blocks
-- statement:
--   In the standing proof regime, if a new catalogue rule $w\notin F$ is adjacent to some rule of a finite catalogue set $F$, then
--   $$c(F\cup\{w\})\le c(F)+(2t-1).$$
--   Consequently every nonempty finite catalogue set $B$ connected by rule adjacencies satisfies
--   $$c(B)\le(2t-1)|B|+1.$$
--   Rule adjacency is sharing a de Bruijn vertex, and $c$ counts the uncancelled support graph components. The two clauses concern different graphs and retain both the incremental and connected-set bounds.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
--   - encoding: a new rule and a connected rule set → w∉F and ConnectedRules B, including nonemptiness; reason: new excludes an existing member, while connected blocks in the source are nonempty
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 4.5, printed p. 13 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_SupportComponents
import Definitions.Def_DeletionHash_MixedEdit_Regime

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 4.5, both the adjunction estimate and its nonempty connected-set consequence. -/
theorem connected_blocks {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L) :
    (∀ F : Finset (Spectrum α L), (∀ z ∈ F, z ∈ Catalogue k L t b) →
      ∀ w : Spectrum α L, w ∈ Catalogue k L t b → w ∉ F →
        (∃ z ∈ F, RuleAdjacent w z) →
        componentCount (insert w F) ≤ componentCount F + (2*t-1)) ∧
    (∀ B : Finset (Spectrum α L), (∀ z ∈ B, z ∈ Catalogue k L t b) →
      ConnectedRules B → componentCount B ≤ (2*t-1)*B.card+1) := by sorry

end DeletionHash.MixedEdit
