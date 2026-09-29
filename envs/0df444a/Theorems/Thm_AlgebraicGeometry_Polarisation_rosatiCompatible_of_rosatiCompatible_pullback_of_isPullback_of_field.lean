-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field
-- name    : AlgebraicGeometry.Polarisation.rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/da574b00-8fa7-57df-b5dc-66b44d1cc50a
-- title:
--   Descent of Rosati compatibility along a field extension
-- statement:
--   Let $k$ and $k'$ be fields with $k'$ a $k$-algebra, and let $A, A'$ be schemes (in universe $0$). Let $f : A \to \operatorname{Spec} k$ carry a relative group law $L$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} k$, with the group axioms and naturality) and satisfy `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper with connected fibres and admits a relative group law; let $f' : A' \to \operatorname{Spec} k'$ carry a relative group law $L'$. Let $g : A' \to A$ exhibit the square $g, f', f, \operatorname{Spec}(k \to k')$ as a pullback, and assume $g$ is multiplicative: for every $T$-point base map $t'$ over $\operatorname{Spec} k'$ and all $P, Q \in \mathrm{Hom}_{t'}(T, A')$, the product $L'.\mathrm{mul}\,t'\,P\,Q$ followed by $g$ equals the $L$-product of $P$ followed by $g$ and $Q$ followed by $g$ over the composed base map. Let $I$ be a type, $act : I \to \mathrm{End}(A)$ with each $act\,x$ over $f$, $act' : I \to \mathrm{End}(A')$ with each $act'\,x$ over $f'$, such that $act'\,x$ followed by $g$ equals $g$ followed by $act\,x$, and let $star : I \to I$. Let $\mathcal{L}$ be an invertible $\mathcal{O}_A$-module. If `RosatiCompatible` holds for $f', L', g^{*}\mathcal{L}, act', star$ — that is, for each $b \in I$ the two pullbacks of the Mumford bundle $m^{*}g^{*}\mathcal{L} \otimes \mathrm{pr}_1^{*}(g^{*}\mathcal{L})^{\vee} \otimes \mathrm{pr}_2^{*}(g^{*}\mathcal{L})^{\vee}$ on $A' \times_{k'} A'$ along $(\mathrm{id}, act'\,b)$ and along $(act'(star\,b), \mathrm{id})$ are isomorphic over some open neighbourhood of each point of $\operatorname{Spec} k'$ — then the same holds for $f, L, \mathcal{L}, act, star$ over $\operatorname{Spec} k$.
--
--   This is the descent of Rosati compatibility of a polarising invertible sheaf with a family of endomorphisms along a field extension: the symmetry condition $(\mathrm{id} \times \iota b)^{*}\Lambda(\mathcal{L}) \cong (\iota(b^{\star}) \times \mathrm{id})^{*}\Lambda(\mathcal{L})$ for the Mumford bundle $\Lambda$ may be checked after base change to $k'$. It is used in the construction of fake elliptic curves with quaternionic multiplication, where the compatibility is first verified over an algebraic closure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.rosatiCompatible_of_rosatiCompatible_pullback_of_isPullback_of_field
    (k k' : Type) [Field k] [Field k'] [Algebra k k']
    {A A' : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (f' : A' ⟶ Spec (CommRingCat.of k')) (L' : RelativeGroupLaw k' f')
    (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of k')) (P Q : SchemeHomOver t' f'),
      (L'.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act' : I → (A' ⟶ A')) (act_over' : ∀ x : I, act' x ≫ f' = f')
    (hact : ∀ x : I, act' x ≫ g = g ≫ act x) (star : I → I)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h : RosatiCompatible f' L' ((Scheme.Modules.pullback g).obj 𝓛) act' act_over' star) :
    RosatiCompatible f L 𝓛 act act_over star := by sorry
