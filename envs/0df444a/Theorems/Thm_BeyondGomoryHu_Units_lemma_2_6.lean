-- Prove2me | Theorems.Thm_BeyondGomoryHu_Units_lemma_2_6
-- name    : BeyondGomoryHu.Units.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:50.996097+00:00
-- url     : https://prove2.me/theorems/577c0ffa-ce30-486a-9602-bce34997479a
-- title:
--   Lemma 2.6 — four components lemma (corrected: S-cut meets S on both sides)
-- statement:
--   Let $G$ be a connected undirected graph with positive integer weights, $S,T,W\subseteq V$, $A$ an $S$-mincut, $B$ a $T$-mincut and $C$ a $W$-mincut. Consider the four sets
--   $$A\setminus(B\cup C),\quad B\setminus(A\cup C),\quad C\setminus(A\cup B),\quad A\cap B\cap C.$$
--   If three distinct ones among them are an $S$-cut, a $T$-cut and a $W$-cut respectively, then the fourth is empty.
--
--   The lemma is the three-cut counterpart of Lemma 2.5 and drives Lemmas 3.10, 4.5, 6.9 and 6.10.
--
--   **Formalization Note.** The four sets are `fourComponents A B C` in the displayed order; `i, j, l, m` are the four distinct positions.
--
--   Differences from the source:
--   - correction: an S-cut is a set A with A ∩ S = ∅ and Ā ∩ S ≠ ∅ (p. 3, as printed) → an S-cut meets S on both sides: A ∩ S ≠ ∅ and Ā ∩ S ≠ ∅ (IsCut); reason: as printed, A = ∅ is an S-cut of capacity 0, so in the connected path a–b (weight 1) with S = {a,b} the only S-mincut is ∅; then no (x,y)-mincut exists and Theorem 2.2 fails; every proof (e.g. App. B, "s1 ∈ S ∩ A, s2 ∈ S ∩ Ā") uses the corrected definition
--   - encoding: G = (V, E, w) with w : E → Z+ → a finite vertex type V (Fin n in the goal) and a symmetric weight function w : V → V → ℕ, 0 meaning no edge; reason: same capacities of every vertex set: parallel edges add up and loops cross no cut
-- source:
--   Koustav Bhanja, Merav Parter, Asaf Petruschka, STOC 2027 submission #1544 (October 2026), Lemma 2.6 (Four Components Lemma), p. 4 (PDF 6); proof in Appendix B, p. 33 (PDF 35)

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false

namespace BeyondGomoryHu.Units

theorem lemma_2_6 {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (S T W A B C : Finset V)
    (hA : IsMincut G S A) (hB : IsMincut G T B) (hC : IsMincut G W C)
    (i j l m : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m)
    (hlm : l ≠ m) (hi : IsCut S (fourComponents A B C i)) (hj : IsCut T (fourComponents A B C j))
    (hl : IsCut W (fourComponents A B C l)) :
    fourComponents A B C m = ∅ := by sorry

end BeyondGomoryHu.Units
