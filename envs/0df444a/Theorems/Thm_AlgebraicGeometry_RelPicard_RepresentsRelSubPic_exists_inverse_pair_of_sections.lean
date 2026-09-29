-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_sections
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_inverse_pair_of_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/4584f2f4-e413-5dda-9be0-6521c7c9e195
-- title:
--   Independence of the Pic⁰ representing scheme from the rigidifying section
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c : C \to \operatorname{Spec} R$ a morphism, and let $\varepsilon,\varepsilon'$ be two sections of $c$ (morphisms $\operatorname{Spec} R \to C$ composing with $c$ to the identity). Let $D,D'$ be pointed $R$-schemes in the sense of `RelativePic0Designation`, each consisting of a scheme with a structure morphism to $\operatorname{Spec} R$ and a section of it. Assume $D$ represents, via `RepresentsRelSubPic`, the cut `algEquivZeroCut c ε` of the relative Picard functor of $c$ rigidified along $\varepsilon$: there is a Poincaré bundle on $C \times_R D.P$, invertible and trivialised along the rigidifying section, satisfying `FibrewiseAlgEquivZero`, such that for every $R$-scheme $t : T \to \operatorname{Spec} R$ and every $\varepsilon$-rigidified invertible module $M$ on $C\times_R T$ satisfying `FibrewiseAlgEquivZero` (for every algebraically closed field $k$ and every $k$-point of $T$, the restriction of $M$ to the geometric fibre is joined to the trivial bundle by an algebraic family over a geometrically integral $k$-scheme locally of finite type, as in `IsAlgEquivZero`) there is a unique $R$-morphism $T \to D.P$ pulling the Poincaré bundle back to a module isomorphic to $M$, and the zero section pulls it back to the unit module; assume likewise that $D'$ represents the corresponding cut for $\varepsilon'$. Then there exist $R$-morphisms $\theta : D.P \to D'.P$ and $\theta' : D'.P \to D.P$ with $\theta$ followed by $\theta'$ the identity of $D.P$ and $\theta'$ followed by $\theta$ the identity of $D'.P$, such that moreover for every $R$-scheme $t : T \to \operatorname{Spec} R$, every $\varepsilon$-rigidified $M$ and $\varepsilon'$-rigidified $N$ on $C\times_R T$ both satisfying `FibrewiseAlgEquivZero`, and every invertible module $Q$ on $T$ admitting an isomorphism $N \cong M \otimes p_T^{*}Q$ with $p_T : C\times_R T \to T$ the projection, the classifying morphism of $M$ followed by $\theta$ equals the classifying morphism of $N$.
--
--   This is the statement that the scheme representing the fibrewise-algebraically-trivial part of the relative Picard functor does not depend on the choice of rigidificator, the comparison isomorphism being the one induced by re-rigidification $M \mapsto M \otimes p_T^{*}Q$; the compatibility clause identifies it on classifying morphisms. It is used in the construction of the Néron-model property bundle for the Jacobians of the modular curves $X_H$ and in comparing points of these curves under degeneracy morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_sections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_inverse_pair_of_sections
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (ε ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D D' : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c ε' (algEquivZeroCut c ε') D') :
    ∃ (θ : SchemeHomOver D.toBase D'.toBase) (θ' : SchemeHomOver D'.toBase D.toBase),
      θ.1 ≫ θ'.1 = 𝟙 D.P ∧ θ'.1 ≫ θ.1 = 𝟙 D'.P ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ M.L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj Q) →
        postComp θ (h.classify t M hM) = h'.classify t N hN := by sorry
