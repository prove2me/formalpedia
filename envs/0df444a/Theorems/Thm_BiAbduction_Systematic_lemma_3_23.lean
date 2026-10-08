-- Prove2me | Theorems.Thm_BiAbduction_Systematic_lemma_3_23
-- name    : BiAbduction.Systematic.lemma_3_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:27.608353+00:00
-- url     : https://prove2.me/theorems/f2a01bef-c94c-4768-890e-70c5cf2f6dee
-- title:
--   Lemma 3.23 — properties of subtraction F − G = F ∧ ¬((¬emp) ∗ G)
-- statement:
--   For arbitrary predicates $F,G,H,F_1,\dots,F_n$ and a variable $X$, with $F-G=F\wedge\neg((\neg\mathsf{emp})*G)$:
--
--   1. $\min(F)=F-F$;
--   2. $(F\vee G)-H=(F-H)\vee(G-H)$;
--   3. $(\exists X.F)-G=\exists X.(F-G)$, provided $X$ is not free in $G$;
--   4. $F-(G\vee H)=(F-G)\wedge(F-H)$;
--   5. $F-(\exists X.G)=\forall X.(F-G)$, provided $X$ is not free in $F$;
--   6. $\min(F_1\vee\dots\vee F_n)=G_1\vee\dots\vee G_n$, where $G_i=((F_i-F_1)\cdots-F_n)$.
--
--   Property (6) reduces the computation of $\min$ of a disjunction to binary subtraction, the third phase of the systematic algorithm.
--
--   **Formalization Note** In (6) the disjunction is over a list $F_1,\dots,F_n$ (possibly empty) and $G_i$ is the left fold of subtraction starting from $F_i$.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), p. 32, Lemma 3.23 (1)–(6)

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Semantics

namespace BiAbduction.Systematic

/-- Lemma 3.23 (p. 32), properties of subtraction, for arbitrary predicates:
(1) `min(F) = F − F`; (2) `(F ∨ G) − H = (F − H) ∨ (G − H)`;
(3) `(∃X.F) − G = ∃X.(F − G)` if `X` is not free in `G`; (4) `F − (G ∨ H) = (F − G) ∧ (F − H)`;
(5) `F − (∃X.G) = ∀X.(F − G)` if `X` is not free in `F`;
(6) `min(F₁ ∨ ⋯ ∨ Fₙ) = G₁ ∨ ⋯ ∨ Gₙ` with `Gᵢ = ((Fᵢ − F₁) ⋯ − Fₙ)`. -/
theorem lemma_3_23 :
    (∀ F : Pred, minSet F = subP F F) ∧
    (∀ F G H : Pred, subP (F ∪ G) H = subP F H ∪ subP G H) ∧
    (∀ (X : ℕ) (F G : Pred), NotFree X G → subP (exQ X F) G = exQ X (subP F G)) ∧
    (∀ F G H : Pred, subP F (G ∪ H) = subP F G ∩ subP F H) ∧
    (∀ (X : ℕ) (F G : Pred), NotFree X F → subP F (exQ X G) = allQ X (subP F G)) ∧
    (∀ Fs : List Pred,
      minSet (⋃ i : Fin Fs.length, Fs.get i) =
        ⋃ i : Fin Fs.length, Fs.foldl subP (Fs.get i)) := by sorry

end BiAbduction.Systematic
