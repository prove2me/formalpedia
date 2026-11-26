-- Prove2me | Theorems.Thm_CategoryTheory_Functor_rightDerived_linear_of_linear
-- name    : CategoryTheory.Functor.rightDerived_linear_of_linear
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-26T21:22:52.264812+00:00
-- url     : https://prove2.me/theorems/173cde2b-d74d-5baf-ac24-e050809eba0d
-- title:
--   Right derived functors of an $R$-linear functor are $R$-linear: $R^nF(r \cdot f) = r \cdot R^nF(f)$
-- statement:
--   Let $R$ be a semiring and let $\mathcal C$ and $\mathcal D$ be $R$-linear abelian categories, where every object of $\mathcal C$ has an injective resolution. Let $F\colon \mathcal C \to \mathcal D$ be an additive functor that is $R$-linear, that is $F(r \cdot f) = r \cdot F(f)$ for every morphism $f$ of $\mathcal C$ and every $r \in R$. Then for every $n \ge 0$ the $n$-th right derived functor $R^nF\colon \mathcal C \to \mathcal D$ is $R$-linear as well:
--
--   $$R^nF(r \cdot f) = r \cdot R^nF(f) \qquad \text{for all morphisms } f \text{ of } \mathcal C \text{ and all } r \in R.$$
--
--   Indeed, $R^nF(X)$ is the $n$-th cohomology of $F$ applied to an injective resolution $X \to I^\bullet$; the morphism $r \cdot \mathrm{id}_{I^\bullet}$ lifts $r \cdot \mathrm{id}_X$, so $R^nF(r \cdot \mathrm{id}_X) = H^n(F(r \cdot \mathrm{id}_{I^\bullet})) = r \cdot \mathrm{id}$ because $F$ and cohomology are $R$-linear, and $R^nF(r \cdot f) = R^nF(f) \circ R^nF(r \cdot \mathrm{id}_X)$. A typical use: for a ring $\Lambda$ and a morphism of sites, the higher direct images and the cohomology functors on sheaves of $\Lambda$-modules are $\Lambda$-linear, so the derived-functor groups are $\Lambda$-modules and the maps between them are $\Lambda$-linear.
--
--   **Formalization Note**: $R$-linearity of categories and functors is Mathlib's `CategoryTheory.Linear R` and `Functor.Linear R`; $R^nF$ is `Functor.rightDerived n`, built from Mathlib's chosen injective resolutions (`HasInjectiveResolutions C`, which holds for instance when $\mathcal C$ is abelian with enough injectives); `F.Additive` is needed to form `rightDerived`. The conclusion is the `Prop`-valued class `(F.rightDerived n).Linear R`. The statement is not vacuous: $R = \mathbb Q$, $\mathcal C = \mathcal D = $ `ModuleCat.{0} ℚ` and $F$ the identity functor satisfy every hypothesis.
-- source:
--   C. A. Weibel, An Introduction to Homological Algebra, §2.5 (right derived functors); A. Grothendieck, Sur quelques points d'algèbre homologique, Tôhoku Math. J. 9 (1957), Chapter II

import Mathlib

set_option autoImplicit false

universe w v v' u u'

open CategoryTheory Limits

theorem CategoryTheory.Functor.rightDerived_linear_of_linear
    {R : Type w} [Semiring R]
    {C : Type u} [Category.{v} C] [Abelian C] [CategoryTheory.Linear R C] [HasInjectiveResolutions C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [CategoryTheory.Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] (n : ℕ) :
    (F.rightDerived n).Linear R := by
  sorry
