-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/6bc56701-eca0-5b4c-9e0f-5023dbe78cd2
-- title:
--   Theorem of the cube over an affine base, pull-back form
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec} S$ be a morphism. Let $L$ be a relative group law for $f$: functorially in a scheme $T$ with a structure morphism $t : T \to \operatorname{Spec} S$, a multiplication, a unit and an inversion on the set $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $\operatorname{Spec} S$, satisfying associativity, both unit laws and left inverse, with multiplication compatible with composition $T' \to T$ over $\operatorname{Spec} S$; assume in addition $L$ is commutative, i.e. its multiplication is commutative on each such set of points. Assume the bundle of abelian-scheme properties for $f$: $f$ is smooth, proper, each fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} S$ is connected, and a relative group law for $f$ exists. Let $\mathcal{L}$ be a module on $A$ which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ over which the restriction of $\mathcal{L}$ along $U \hookrightarrow A$ is isomorphic to the unit module of $U$. Let $Y$ be a scheme over $\operatorname{Spec} S$, with structure morphism $Y.\mathrm{hom}$, and let $g_1, g_2, g_3 : Y \to A$ be three morphisms over $\operatorname{Spec} S$, multiplied using the group-object structure on $A$ over $\operatorname{Spec} S$ that $L$ induces. Then the type of isomorphisms of modules on $Y$
--   $$(g_1g_2g_3)^*\mathcal{L} \otimes g_1^*\mathcal{L} \otimes g_2^*\mathcal{L} \otimes g_3^*\mathcal{L} \;\cong\; (g_1g_2)^*\mathcal{L} \otimes (g_1g_3)^*\mathcal{L} \otimes (g_2g_3)^*\mathcal{L} \otimes Y.\mathrm{hom}^* e^*\mathcal{L}$$
--   is non-empty, where $e : \operatorname{Spec} S \to A$ is the unit of $L$ at the identity morphism of $\operatorname{Spec} S$.
--
--   This is the theorem of the cube in pull-back form over an arbitrary affine base, stated for relative group laws and invertible modules; the correction factor $Y.\mathrm{hom}^*e^*\mathcal{L}$, pulled back from the base, is trivial over an algebraically closed field but genuinely present in general (for $\mathcal{L} = f^*M$ both sides become $Y.\mathrm{hom}^*M^{\otimes 4}$). It is used in the construction of polarisations, where it feeds the lemmas identifying slices of the Mumford bundle and its dual as locally trivial along the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation
open scoped CategoryTheory.MonObj

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_mul_mul_tensor_iso_tensor_pullback_one_of_commRing
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {Y : Over (Spec (CommRingCat.of S))} (g₁ g₂ g₃ : Y ⟶ Over.mk f) :
    letI := L.grpObjOverMk
    Nonempty (
      (Scheme.Modules.pullback (g₁ * g₂ * g₃).left).obj 𝓛 ⊗ (Scheme.Modules.pullback g₁.left).obj 𝓛 ⊗
          (Scheme.Modules.pullback g₂.left).obj 𝓛 ⊗ (Scheme.Modules.pullback g₃.left).obj 𝓛 ≅
        (Scheme.Modules.pullback (g₁ * g₂).left).obj 𝓛 ⊗ (Scheme.Modules.pullback (g₁ * g₃).left).obj 𝓛 ⊗
          (Scheme.Modules.pullback (g₂ * g₃).left).obj 𝓛 ⊗
            (Scheme.Modules.pullback Y.hom).obj
              ((Scheme.Modules.pullback (L.one (𝟙 (Spec (CommRingCat.of S)))).1).obj 𝓛)) := by sorry
