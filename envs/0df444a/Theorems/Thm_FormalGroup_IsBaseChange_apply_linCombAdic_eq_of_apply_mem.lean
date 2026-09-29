-- Prove2me | Theorems.Thm_FormalGroup_IsBaseChange_apply_linCombAdic_eq_of_apply_mem
-- name    : FormalGroup.IsBaseChange.apply_linCombAdic_eq_of_apply_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/d33d8538-72de-5314-bed7-b3d2c2e876a2
-- title:
--   Base change of adic formal linear combinations [a]x₀+[b]x₁
-- statement:
--   Let $A$ and $B$ be commutative rings, $I\subseteq A$ and $J\subseteq B$ ideals, and assume $A$ is $I$-adically complete and $B$ is $J$-adically complete (in Mathlib's sense `IsAdicComplete`). Let $\chi\colon A\to B$ be a ring homomorphism, subject to no continuity or compatibility condition relating $I$ and $J$. Let $F$ be a one-dimensional formal group law over $A$ and $G$ one over $B$, and assume the project's relation `F.IsBaseChange χ G`, which by definition says that the two-variable power series of $G$ is the coefficientwise image of that of $F$ under $\chi$, i.e. $G=\mathrm{map}\,\chi\,(F)$. Let $x_0,x_1\in I$ with $\chi(x_0),\chi(x_1)\in J$, and let $a,b$ be natural numbers. Here `linCombAdic` of a formal group over a ring, relative to an ideal, is the element $F(\,[a]_Fx_0,\,[b]_Fx_1\,)$ obtained by evaluating the group law and its iterates ($[0]_Fx=0$, $[n+1]_Fx=F([n]_Fx,x)$) using the adic uniform structure attached to that ideal. The conclusion is $\chi\bigl(F.\mathtt{linCombAdic}\ I\ x_0\ x_1\ a\ b\bigr)=G.\mathtt{linCombAdic}\ J\ (\chi x_0)\ (\chi x_1)\ a\ b$: the formal linear combination computed $I$-adically in $A$ is carried by $\chi$ to the corresponding combination computed $J$-adically in $B$.
--
--   This is the base-change compatibility of formal-group linear combinations $[a]_Fx_0+_F[b]_Fx_1$ under an arbitrary ring homomorphism, the point being that only the two elements $x_0,x_1$ are required to have images in $J$, no inclusion $\chi(I)\subseteq J$ being assumed. It is used in the construction and transport of Drinfeld bases for level structures on modular curves, in the existence statements for Drinfeld bases over subtypes of the relevant moduli packages.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_IsBaseChange_apply_linCombAdic_eq_of_apply_mem.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open FormalGroup

theorem FormalGroup.IsBaseChange.apply_linCombAdic_eq_of_apply_mem
    {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete J B]
    (χ : A →+* B) (F : FormalGroup A) (G : FormalGroup B) (h : F.IsBaseChange χ G)
    (x₀ x₁ : A) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (hχ₀ : χ x₀ ∈ J) (hχ₁ : χ x₁ ∈ J) (a b : ℕ) :
    χ (F.linCombAdic I x₀ x₁ a b) = G.linCombAdic J (χ x₀) (χ x₁) a b := by sorry
