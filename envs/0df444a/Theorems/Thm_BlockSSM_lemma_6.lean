-- Prove2me | Theorems.Thm_BlockSSM_lemma_6
-- name    : BlockSSM.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:29:55.361435+00:00
-- url     : https://prove2.me/theorems/94f01e31-e283-4dc9-bbf6-f22352a1bc4c
-- title:
--   Lemma 6: group extraction
-- statement:
--   In the setting of Lemma 5, an idempotent of least affine rank in $M$ exists. Let $E$ be any such idempotent, with $\mathrm{rank}\,F=\dim F(V)$. Then:
--
--   1. $H=EME=\{EXE:X\in M\}$ is a group under the multiplication of $M$, with identity $E$: it contains $E$, is closed under multiplication, $E$ is a two-sided identity on it, and each of its elements has a two-sided inverse in it;
--   2. $H$ acts on $V_E=E(V)$, and the action is faithful: two elements of $H$ that agree on $V_E$ are equal;
--   3. $H$ surjects onto $G$: for a homomorphism $\pi:M\to G$ as in Lemma 5 and any $g\in G$, some $F\in H$ has $\pi(F)=g$.
--
--   This step isolates a reversible part of the dynamics, without assuming that any transition is invertible.
--
--   **Formalization Note** The group structure is stated through its axioms on the subset $EME$ of $M$. The existence of $E$ is included so that the rest is not vacuous; "least" is among idempotents of $M$.
--
--   Differences from the source:
--   - reading: "an idempotent of least affine rank" → least among the idempotents of $M$; reason: the source's proof applies minimality to an idempotent power; the two readings give the same value, because every element of a finite monoid has an idempotent power of no larger rank
--   - generalization: an integer block bound $b\ge 1$ → an arbitrary $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`); reason: every integer $b\ge 1$ is a case through the cast; the lemma does not use $b\ge 1$
--   - encoding: hidden state space $\mathbb C^n$ with block-diagonal $A_g$ → the product $\prod_i\mathbb C^{n_i}$ with one matrix per block; reason: the same space split along the partition; the linear part is block-diagonal by construction
--   - encoding: the group $H=EME$ → a subset of $M$ together with the group axioms for it; reason: the same data; a group structure on the subset is equivalent to these clauses
--   - reading: "Let $E\in M$ be an idempotent of least affine rank" (existence presupposed) → existence of such an $E$ asserted as a first conjunct; reason: makes the remaining clauses non-vacuous; it is the stronger reading, and dropping the conjunct gives the source's claim
--   - encoding: a word $s=g_1\cdots g_T$ → a list with $g_1$ at the head; reason: the same words; the empty list is the empty word
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 6, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BlockSSM_Tracker_Tracks
import Definitions.Def_BlockSSM_Tracker_IsLeastRankIdempotent
import Definitions.Def_BlockSSM_Tracker_corner

universe u

namespace BlockSSM

/-- **Lemma 6 (Group extraction).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 6, p.3 (PDF p.4): "Let E ∈ M be an idempotent of least
affine rank, where rank F = dim F(V). Then H = EME is a group with identity E, acts faithfully on
V_E = E(V), and surjects onto G."

**Formalization Note.** The first clause says such an `E` exists, so the rest is not vacuous. For
every such `E`, the next four clauses say that `EME` is a group under the multiplication of `M` with
identity `E` (it contains `E`, it is closed, `E` is two-sided identity, every element has a two-sided
inverse in it); the next two that it acts on `E(V)` and that two elements agreeing on `E(V)` are equal;
the last that the homomorphism of Lemma 5 maps it onto `G`. Lemma 5 supplies such a `p`. -/
theorem lemma_6 {G : Type u} [Group G] [Finite G] {b : ℕ∞} (T : Tracker G b) (ht : T.Tracks)
    (hf : T.IsFiniteState) :
    (∃ E, T.IsLeastRankIdempotent E) ∧
    ∀ E, T.IsLeastRankIdempotent E →
      E ∈ T.corner E ∧
      (∀ F ∈ T.corner E, ∀ F' ∈ T.corner E, F * F' ∈ T.corner E) ∧
      (∀ F ∈ T.corner E, E * F = F ∧ F * E = F) ∧
      (∀ F ∈ T.corner E, ∃ F' ∈ T.corner E, F * F' = E ∧ F' * F = E) ∧
      (∀ F ∈ T.corner E, Set.MapsTo F.1 (Set.range E.1) (Set.range E.1)) ∧
      (∀ F ∈ T.corner E, ∀ F' ∈ T.corner E, (∀ x ∈ Set.range E.1, F.1 x = F'.1 x) → F = F') ∧
      (∀ p : T.transMonoid →* G, (∀ s : List G, p (T.wordElt s) = wordProd s) →
        ∀ g : G, ∃ F ∈ T.corner E, p F = g) := by sorry

end BlockSSM
