-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_thetaGroup_mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso
-- name    : AlgebraicGeometry.RiemannForm.thetaGroup.mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/bef5a701-f525-570a-bd4c-b8485ef134d4
-- title:
--   Lifts of 2-torsion commute in G(mathcal L₀^{⊗ 2})
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$ on $f$ (functorial multiplication, unit, inverse on $T$-points of $f$, compatible with base change) which is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle k f`, i.e. $f$ is smooth and proper, every fibre of $f$ is connected, and $f$ carries some relative group law. Let $\mathcal L_0$ be a module on $A$ which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ over which the pullback of $\mathcal L_0$ along $U \hookrightarrow A$ is isomorphic to the unit module. Assume further that for every $Q$ in the additive group $A(k)$ of $k$-points of $f$ with $2Q = 0$, the pullback of $\mathcal L_0$ along the translation morphism by $Q$ is isomorphic to $\mathcal L_0$. Let $g, g'$ be elements of the theta group of $\mathcal L_0 \otimes \mathcal L_0$, that is, pairs consisting of an automorphism of the pair $(A, \mathcal L_0 \otimes \mathcal L_0)$ and a point of $A(k)$ such that the automorphism has translation by that point as its underlying morphism of $A$; suppose the points $\operatorname{pt}(g)$ and $\operatorname{pt}(g')$ underlying $g$ and $g'$ are both killed by $2$. Then $g g' = g' g$.
--
--   This is the commutativity, in Mumford's theta group of $\mathcal L_0^{\otimes 2}$, of lifts of $2$-torsion points, under the hypothesis that $\mathcal L_0$ is fixed by translation by all $2$-torsion; it is the step that makes the $2$-torsion part of the theta group abelian. It is used in the construction of a subgroup of the theta group of $\mathcal L_0 \otimes \mathcal L_0$ mapping bijectively onto the $2$-torsion subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_thetaGroup_mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.thetaGroup.mul_comm_of_two_torsion_of_forall_two_torsion_pullback_translation_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (hK2 : ∀ Q : L.AlgPoints hc k, 2 • Q = 0 →
      Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛₀ ≅ 𝓛₀))
    (g g' : thetaGroup f L hc (𝓛₀ ⊗ 𝓛₀))
    (hg : 2 • Multiplicative.toAdd (thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) g) = 0)
    (hg' : 2 • Multiplicative.toAdd (thetaGroup.pt f L hc (𝓛₀ ⊗ 𝓛₀) g') = 0) :
    g * g' = g' * g := by sorry
