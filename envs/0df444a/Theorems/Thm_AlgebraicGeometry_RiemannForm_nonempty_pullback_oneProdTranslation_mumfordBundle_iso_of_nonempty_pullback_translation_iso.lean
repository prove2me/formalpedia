-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_nonempty_pullback_oneProdTranslation_mumfordBundle_iso_of_nonempty_pullback_translation_iso
-- name    : AlgebraicGeometry.RiemannForm.nonempty_pullback_oneProdTranslation_mumfordBundle_iso_of_nonempty_pullback_translation_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/ecebc8cf-1ad0-5187-a66e-b6e5eba0c620
-- title:
--   Invariance of the Mumford bundle under 1× T_Q
-- statement:
--   Let $k$ be an algebraically closed field (in the bottom universe), let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, and let $L$ be a relative group law on $f$: a functorial group structure on the sets of $T$-valued points $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ over varying $t : T \to \operatorname{Spec} k$, compatible with base change along $T' \to T$; assume $L$ is commutative, and that $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on $f$ exists. Let $\mathcal L$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit module, let $g$ be a natural number such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and let $Q$ be a $k$-point of $A$, i.e. an element of the additive group of sections of $f$ over $\operatorname{Spec}$ of the identity of $k$. Write $T_Q : A \to A$ for the translation $(L.\mathrm{mul}\,f\,\mathrm{id}\,(\text{constant } Q))$ and $\tau$ for the morphism $1 \times T_Q$ of $A \times_{k} A$ determined by $\tau$ followed by $\mathrm{pr}_1$ being $\mathrm{pr}_1$ and $\tau$ followed by $\mathrm{pr}_2$ being $\mathrm{pr}_2$ followed by $T_Q$. Assume $T_Q^{*}\mathcal L \cong \mathcal L$ (the type of such isomorphisms is nonempty). Then $\tau^{*}\Lambda(\mathcal L) \cong \Lambda(\mathcal L)$, where $\Lambda(\mathcal L) = m^{*}\mathcal L \otimes (\mathrm{pr}_1^{*}\mathcal L^{\vee} \otimes \mathrm{pr}_2^{*}\mathcal L^{\vee})$ is the Mumford bundle on $A \times_k A$, $m$ being the addition morphism of $L$ and $\mathcal L^{\vee}$ the internal hom from $\mathcal L$ to the unit module.
--
--   This is the elementary invariance step for the Mumford (or theta) bundle $\Lambda(\mathcal L) = m^*\mathcal L \otimes \mathrm{pr}_1^*\mathcal L^\vee \otimes \mathrm{pr}_2^*\mathcal L^\vee$: a point of the stabiliser of $\mathcal L$ acts trivially on $\Lambda(\mathcal L)$ through $1 \times T_Q$. It is used in the construction of the Riemann form and Rosati involution machinery, being cited by [`AlgebraicGeometry.RiemannForm.exists_pullback_oneProdNsmul_iso_mumfordBundle_of_forall_torsion`](thm.html#AlgebraicGeometry.RiemannForm.exists_pullback_oneProdNsmul_iso_mumfordBundle_of_forall_torsion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_nonempty_pullback_oneProdTranslation_mumfordBundle_iso_of_nonempty_pullback_translation_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.RiemannForm.nonempty_pullback_oneProdTranslation_mumfordBundle_iso_of_nonempty_pullback_translation_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (Q : L.AlgPoints hc k)
    (hQ : Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛)) :
    Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).obj (mumfordBundle f L 𝓛) ≅
      mumfordBundle f L 𝓛) := by sorry
