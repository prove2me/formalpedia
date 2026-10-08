-- Prove2me | Theorems.Thm_AlgebraicPCSP_OneInThree_proposition_8_12
-- name    : AlgebraicPCSP.OneInThree.proposition_8_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:15.955534+00:00
-- url     : https://prove2.me/theorems/32f5e699-2470-45d6-ad20-68e158939f5d
-- title:
--   Proposition 8.12 — every almost rectangle is tame
-- statement:
--   Let $D$ be a finite set, $R\subseteq D^3$, $f:\mathbf T\to(D;R)$ and $g:(D;R)\to\mathbf H_2$ homomorphisms, $p$ a prime with $p>60|D|$, and $s:D^p\to D$ a cyclic polymorphism of $(D;R)$. Then every almost rectangle
--   $$X=[\underbrace{k,\dots,k}_{m},l,\dots,l],\qquad 0\le m\le p,\quad 0\le l\le k\le p,\quad k-l\le 5|D|,$$
--   is tame: either $X\sim 0_{p\times p}$ and $\lambda(X)<1/3$, or $X\sim 1_{p\times p}$ and $\lambda(X)>1/3$.
--
--   Proposition 8.12 is what makes the two matrices of §8.4 comparable with $0_{p\times p}$ and $1_{p\times p}$, which produces the contradiction.
--
--   **Formalization Note** Column heights range over $0\le k_j\le p$; Definition 8.11 prints $1\le k_j\le p$ but the proof of Lemma 8.14 uses height $0$.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 55, Proposition 8.12 (with Definition 8.11)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_OneInThree_Structures
import Definitions.Def_AlgebraicPCSP_OneInThree_Matrices

namespace AlgebraicPCSP.OneInThree

open PCSPBLPAff.Symmetric

/-- Proposition 8.12 (p. 55): each almost rectangle (step size at most `5|D|`) is tame, for a
cyclic polymorphism `s` of the finite structure `(D; R)` of prime arity `p > 60|D|` and
homomorphisms `f : T → (D; R)`, `g : (D; R) → H₂`. -/
theorem proposition_8_12 {D : Type} [Fintype D] [DecidableEq D] (R : Set (Fin 3 → D))
    (f : Fin 2 → D) (g : D → Fin 2)
    (hf : IsHom oneInThree (ternaryStruct R) f) (hg : IsHom (ternaryStruct R) nae g)
    {p : ℕ} (hp : p.Prime) (hpD : 60 * Fintype.card D < p)
    (s : (Fin p → D) → D) (hs : IsPolymorphism (ternaryStruct R) (ternaryStruct R) s)
    (hcyc : IsCyclic s) (X : Fin p → Fin p → Fin 2)
    (hX : IsAlmostRectangle (5 * Fintype.card D) X) :
    IsTame f g s X := by sorry

end AlgebraicPCSP.OneInThree
