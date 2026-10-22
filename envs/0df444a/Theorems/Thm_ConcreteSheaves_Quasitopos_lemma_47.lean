-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_lemma_47
-- name    : ConcreteSheaves.Quasitopos.lemma_47
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:08.874394+00:00
-- url     : https://prove2.me/theorems/8c2be956-bbd0-4fad-b910-958913d84073
-- title:
--   Lemma 47, p. 38 — concretization L is left adjoint to the inclusion R
-- statement:
--   Let $D$ be a small category with a coverage $K$ and a terminal object $T$ (written $1$ in the paper), and suppose $(D,K,T)$ is a **concrete site**: representables are sheaves, $\operatorname{hom}(1,-)$ is faithful, and covering families are jointly surjective on points. Write $\underline{X}=X(1)$ for the underlying set of a presheaf $X$ and $\underline{\varphi}:\underline{D}\to\underline{X}$, $d\mapsto X(d)(\varphi)$, for the underlying function of a plot $\varphi\in X(D)$.
--
--   A presheaf $Q$ on $D$ is **concrete** if each map $Q(D)\to Q(1)^{\underline D}$, $\varphi\mapsto\underline\varphi$, is injective. The **concretization** $L(P)$ of a presheaf $P$ has $L(P)(D)$ the set of plots of $P$ modulo $\varphi\sim\varphi'\iff\underline\varphi=\underline{\varphi'}$, with quotient map $\pi_P:P\to L(P)$. Lemma 47 states that $L$ is left adjoint to the inclusion $R$ of concrete presheaves into presheaves; in universal-arrow form, for every presheaf $P$:
--
--   1. $L(P)$ is concrete;
--   2. for every concrete presheaf $Q$ and natural transformation $f:P\to Q$ there is a unique $g:L(P)\to Q$ with $g\circ\pi_P=f$.
--
--   $$
--   \operatorname{Hom}(L(P),Q)\;\cong\;\operatorname{Hom}(P,R(Q))\qquad(Q\text{ concrete}).
--   $$
--
--   Concretization is the first of the two left adjoints used to construct colimits of $D$ spaces.
--
--   **Formalization Note** The site is small ($D$ in universe $u$, presheaves valued in $\mathrm{Type}_u$), covering families are presieves, and the terminal domain is passed explicitly as $(T, h_T)$. The adjunction $L\dashv R$ is stated as the universal property of the unit $\pi_P$, which is equivalent to it; $L(P)(D)$ is encoded as the image of $\varphi\mapsto\underline\varphi$ (definition `concretization`), canonically the quotient of the paper.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, p. 38, Definition 46 and Lemma 47

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits Opposite

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Lemma 47, p. 38. -/
theorem lemma_47 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) (P : Dᵒᵖ ⥤ Type u) :
    IsConcrete T (concretization T P) ∧
      ∀ (Q : Dᵒᵖ ⥤ Type u), IsConcrete T Q → ∀ f : P ⟶ Q,
        ∃! g : concretization T P ⟶ Q, concretizationπ T P ≫ g = f := by sorry

end ConcreteSheaves.Quasitopos
