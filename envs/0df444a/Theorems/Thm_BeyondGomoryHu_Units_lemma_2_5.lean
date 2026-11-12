-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_lemma_2_5
-- name    : BeyondGomoryHu.Units.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:35.52899+00:00
-- url     : https://prove2.me/theorems/a55c4658-5de3-4dee-99d8-bbc4e37bf48e
-- title:
--   Lemma 2.5 — submodularity, posimodularity and hybrid cases for Steiner mincuts (corrected: S-cut meets S on both sides)
-- statement:
--   Let $G$ be a connected undirected graph with positive integer weights, $S,T\subseteq V$, $A$ an $S$-mincut and $B$ a $T$-mincut.
--   1. (Submodularity) If one of $A\cap B$, $A\cup B$ is an $S$-cut and the other a $T$-cut, the former is an $S$-mincut and the latter a $T$-mincut.
--   2. (Posimodularity) If one of $A\setminus B$, $B\setminus A$ is an $S$-cut and the other a $T$-cut, the former is an $S$-mincut and the latter a $T$-mincut.
--   3. (Hybrid) If among the four cuts
--   $$A\cap B,\quad A\cup B,\quad A\setminus B,\quad B\setminus A$$
--   two are $S$-cuts and the other two $T$-cuts, the former two are $S$-mincuts and the latter two $T$-mincuts.
--
--   Moreover, one of the three cases always applies. This is the uncrossing tool used in almost every later proof.
--
--   **Formalization Note.** The four cuts are `fourCuts A B` in the displayed order; the last conjunct is the disjunction of the hypotheses of the three cases.
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Lemma 2.5, p. 4 (PDF 6); proof in Appendix B, p. 33 (PDF 35)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem lemma_2_5 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (S T A B : Finset V)
    (hA : IsMincut G S A) (hB : IsMincut G T B) :
    -- ("Submodularity")
    ((IsCut S (A ∩ B) ∧ IsCut T (A ∪ B) → IsMincut G S (A ∩ B) ∧ IsMincut G T (A ∪ B)) ∧
     (IsCut S (A ∪ B) ∧ IsCut T (A ∩ B) → IsMincut G S (A ∪ B) ∧ IsMincut G T (A ∩ B))) ∧
    -- ("Posimodularity")
    ((IsCut S (A \ B) ∧ IsCut T (B \ A) → IsMincut G S (A \ B) ∧ IsMincut G T (B \ A)) ∧
     (IsCut S (B \ A) ∧ IsCut T (A \ B) → IsMincut G S (B \ A) ∧ IsMincut G T (A \ B))) ∧
    -- ("Hybrid")
    (∀ i j : Fin 4, i ≠ j → IsCut S (fourCuts A B i) → IsCut S (fourCuts A B j) →
      (∀ l : Fin 4, l ≠ i → l ≠ j → IsCut T (fourCuts A B l)) →
      IsMincut G S (fourCuts A B i) ∧ IsMincut G S (fourCuts A B j) ∧
        ∀ l : Fin 4, l ≠ i → l ≠ j → IsMincut G T (fourCuts A B l)) ∧
    -- one of the cases holds
    ((IsCut S (A ∩ B) ∧ IsCut T (A ∪ B)) ∨ (IsCut S (A ∪ B) ∧ IsCut T (A ∩ B)) ∨
     (IsCut S (A \ B) ∧ IsCut T (B \ A)) ∨ (IsCut S (B \ A) ∧ IsCut T (A \ B)) ∨
     (∃ i j : Fin 4, i ≠ j ∧ IsCut S (fourCuts A B i) ∧ IsCut S (fourCuts A B j) ∧
       ∀ l : Fin 4, l ≠ i → l ≠ j → IsCut T (fourCuts A B l))) := by sorry

end BeyondGomoryHu.Units
