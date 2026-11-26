-- Prove2me | Theorems.Thm_CategoryTheory_Adjunction_nonempty_ext_rightDerived_addEquiv_ext_of_isZero_rightDerived_ne
-- name    : CategoryTheory.Adjunction.nonempty_ext_rightDerived_addEquiv_ext_of_isZero_rightDerived_ne
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-26T09:29:05.257041+00:00
-- url     : https://prove2.me/theorems/06a97cbc-6b4a-51ac-b5e2-eedccc30b1e1
-- title:
--   One-row degeneration of the Grothendieck spectral sequence for an exact left adjoint: $\operatorname{Ext}^m(A, R^iN) \cong \operatorname{Ext}^{m+i}(LA, N)$ when $R^qN = 0$ for $q \ne i$
-- statement:
--   Let $\mathcal C$ and $\mathcal D$ be abelian categories, where $\mathcal C$ has enough injectives, and let $L\colon \mathcal D \to \mathcal C$ be left adjoint to $R\colon \mathcal C \to \mathcal D$. Assume that $L$ is exact and that $R$ is additive and left exact, and write $R^q$ for the $q$-th right derived functor of $R$. Let $N$ be an object of $\mathcal C$ and $i \ge 0$ an integer such that $R^qN = 0$ for every $q \ne i$. Then for every object $A$ of $\mathcal D$ and every $m \ge 0$ there is an isomorphism of abelian groups
--
--   $$\operatorname{Ext}^m_{\mathcal D}(A, R^iN) \;\cong\; \operatorname{Ext}^{m+i}_{\mathcal C}(LA, N).$$
--
--   Because $L$ is exact, $R$ sends injectives to injectives and $\operatorname{Hom}_{\mathcal C}(LA, -) = \operatorname{Hom}_{\mathcal D}(A, -) \circ R$, so there is a Grothendieck spectral sequence $E_2^{p,q} = \operatorname{Ext}^p_{\mathcal D}(A, R^qN) \Rightarrow \operatorname{Ext}^{p+q}_{\mathcal C}(LA, N)$. The hypothesis says that its $E_2$ page is concentrated in the single row $q = i$, so it degenerates and gives the isomorphism above. For $i = 0$ this is the acyclic case $\operatorname{Ext}^m(A, RN) \cong \operatorname{Ext}^m(LA, N)$ when $R^qN = 0$ for $q > 0$. A typical use is the Leray spectral sequence of a morphism $f\colon Y \to X$ of sites, with $L = f^{*}$, $R = f_{*}$ and $A$ the constant sheaf: if $R^qf_*F = 0$ for all $q \ne i$, then $H^m(X, R^if_*F) \cong H^{m+i}(Y, F)$ for all $m$.
--
--   **Formalization Note**: $\operatorname{Ext}$ is `CategoryTheory.Abelian.Ext`, with `HasExt.{w}` on both categories (Ext groups in `Type w`). $R^q$ is `Functor.rightDerived q`, computed from Mathlib's injective resolutions, which exist because $\mathcal C$ is abelian with `EnoughInjectives`. Exactness of $L$ is `PreservesFiniteLimits L` and `PreservesFiniteColimits L`; left exactness of $R$ is `PreservesFiniteLimits R`. Additivity of $L$ and $R$ is assumed as instances (`R.Additive` is needed to form `rightDerived`). The instances `PreservesFiniteColimits L`, `PreservesFiniteLimits R` and the two additivity instances hold for every adjunction between abelian categories, so they do not weaken the statement; the real hypotheses are that $L$ preserves finite limits, that $\mathcal C$ has enough injectives, and `hN`. The conclusion asserts that an additive isomorphism exists. The statement is not vacuous: the identity adjunction on `AddCommGrpCat.{0}` with `HasExt.standard`, $A = \mathbb Z$, $N = \mathbb Q$ (an injective group) and $i = 0$ satisfies every hypothesis.
-- source:
--   A. Grothendieck, Sur quelques points d'algèbre homologique, Tôhoku Math. J. 9 (1957), §2.4 (spectral sequence of a composite functor); C. A. Weibel, An Introduction to Homological Algebra, §5.8 (Grothendieck spectral sequence) and §5.2 (collapsing spectral sequences); J. S. Milne, Étale Cohomology, Chapter III §1

import Mathlib

set_option autoImplicit false

universe w v v' u u'

open CategoryTheory Limits Abelian

theorem CategoryTheory.Adjunction.nonempty_ext_rightDerived_addEquiv_ext_of_isZero_rightDerived_ne
    {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasExt.{w} C] [HasExt.{w} D] [EnoughInjectives C]
    {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [R.Additive] [PreservesFiniteLimits R]
    (A : D) (N : C) (i : ℕ) (hN : ∀ q : ℕ, q ≠ i → IsZero ((R.rightDerived q).obj N)) (m : ℕ) :
    Nonempty (Ext A ((R.rightDerived i).obj N) m ≃+ Ext (L.obj A) N (m + i)) := by
  sorry
