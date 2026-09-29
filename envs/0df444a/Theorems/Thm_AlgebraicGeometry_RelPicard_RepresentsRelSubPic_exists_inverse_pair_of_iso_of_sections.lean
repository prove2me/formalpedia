-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_inverse_pair_of_iso_of_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/645c1005-9113-501a-a2af-d116498d83ad
-- title:
--   Transporting Pic⁰ representing schemes along a curve isomorphism
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ be schemes over $R$, and let $\varepsilon$, $\varepsilon'$ be sections of $c$, $c'$ respectively (morphisms $\operatorname{Spec} R \to C$, resp. $\to C'$, composing with the structure morphism to the identity). Let $e : C \cong C'$ be an isomorphism with $e.\mathrm{hom}$ followed by $c'$ equal to $c$ and $e.\mathrm{inv}$ followed by $c$ equal to $c'$. Let $D$, $D'$ be designations, i.e. schemes $D.P$, $D'.P$ over $\operatorname{Spec} R$ each equipped with a section of its structure morphism, and assume $D$ represents the cut `algEquivZeroCut c ε` of the relative Picard functor of $(c,\varepsilon)$ and $D'$ that of $(c',\varepsilon')$: thus $D$ carries a rigidified invertible module on $C \times_R D.P$ satisfying `FibrewiseAlgEquivZero` such that for every $t : T \to \operatorname{Spec} R$ and every $\varepsilon$-rigidified invertible module $M$ on $C \times_R T$ with all geometric fibres algebraically equivalent to zero there is a unique $R$-morphism $T \to D.P$ pulling the Poincaré module back to $M$, with the usual normalisation along the zero section; likewise for $D'$. Then there exist $R$-morphisms $\theta : D.P \to D'.P$ and $\theta' : D'.P \to D.P$, mutually inverse, such that for every $t : T \to \operatorname{Spec} R$, every such $M$ on $C \times_R T$, every such $N$ on $C' \times_R T$, and every invertible module $Q$ on $T$ with $N.L \cong (e^{-1}\times_R T)^{*}M.L \otimes \mathrm{pr}_T^{*}Q$, the classifying morphism of $M$ followed by $\theta$ is the classifying morphism of $N$.
--
--   This is the functoriality of the relative $\mathrm{Pic}^0$ in the curve, in the form that an isomorphism of curves over $\operatorname{Spec} R$ induces an isomorphism of the schemes representing the fibrewise-algebraically-trivial cuts, with no compatibility required between the two rigidifying sections (twisting by an invertible module pulled back from the base is allowed). It is used on the modular curve side to compare Abel–Jacobi maps and to transport Hecke and diamond operators across chart isomorphisms of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_inverse_pair_of_iso_of_sections
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c')
    (e : C ≅ C') (he : e.hom ≫ c' = c) (he' : e.inv ≫ c = c')
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    ∃ (θ : SchemeHomOver D.toBase D'.toBase) (θ' : SchemeHomOver D'.toBase D.toBase),
      θ.1 ≫ θ'.1 = 𝟙 D.P ∧ θ'.1 ≫ θ.1 = 𝟙 D'.P ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
        (N : RigidifiedLineBundle c' ε' t) (hN : FibrewiseAlgEquivZero N)
        (Q : T.Modules), Scheme.Modules.IsInvertible Q →
        Nonempty (N.L ≅ (Scheme.Modules.pullback (curveChange (c := c) (c' := c') e.inv he' t)).obj M.L ⊗
          (Scheme.Modules.pullback (pullback.snd c' t)).obj Q) →
        postComp θ (h.classify t M hM) = h'.classify t N hN := by sorry
