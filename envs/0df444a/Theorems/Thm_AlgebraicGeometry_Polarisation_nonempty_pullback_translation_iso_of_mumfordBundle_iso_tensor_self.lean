-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_translation_iso_of_mumfordBundle_iso_tensor_self
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_translation_iso_of_mumfordBundle_iso_tensor_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/af58e432-b0d4-5506-b538-54c5be4e3d51
-- title:
--   Two-torsion points stabilise mathcal L₀ when Λ(mathcal L₀)congPotimesP
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, and let $L$ be a relative group law on $f$, that is, a functorial group structure on the sets of $T$-valued points of $A$ over $\operatorname{Spec} k$, assumed commutative ($hc$). Assume the bundle `AbelianSchemePropertyBundle k f`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law; assume further that for a natural number $g$ every fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $\mathcal P$ be a module on $A \times_{\operatorname{Spec} k} A$ that is invertible in the sense of admitting local trivialisations by the unit module, and assume $\mathcal P$ is bi-rigidified: its pullback along the slice at the zero point of `L.AlgPoints hc k` is isomorphic to the monoidal unit, as is the pullback along that same slice of the pullback of $\mathcal P$ by the symmetry of $A \times_k A$. Let $\mathcal L_0$ be an invertible module on $A$ and assume the Mumford bundle $m^{*}\mathcal L_0 \otimes (p_1^{*}\mathcal L_0^{\vee} \otimes p_2^{*}\mathcal L_0^{\vee})$, formed with the addition morphism and the two projections of $A \times_k A$, is isomorphic to $\mathcal P \otimes \mathcal P$. Then for every $k$-point $Q$ of the additive group `L.AlgPoints hc k` with $2 \cdot Q = 0$, the pullback of $\mathcal L_0$ along the translation morphism $T_Q$ (the product of the identity point with the constant point $Q$ under $L$) is isomorphic to $\mathcal L_0$.
--
--   The statement says that if the Mumford bundle $\Lambda(\mathcal L_0)$ of an invertible sheaf on an abelian variety is a tensor square of a bi-rigidified invertible sheaf on $A \times_k A$, then every $2$-torsion $k$-point lies in the group $K(\mathcal L_0)$ of translations preserving $\mathcal L_0$. It feeds the halving step for the theta group, being used in the construction of an isomorphism with the Mumford bundle under the hypothesis that $2 \neq 0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_translation_iso_of_mumfordBundle_iso_tensor_self.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_translation_iso_of_mumfordBundle_iso_tensor_self
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _))
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hΛ : Nonempty (mumfordBundle f L 𝓛₀ ≅ 𝓟 ⊗ 𝓟))
    (Q : L.AlgPoints hc k) (hQ : 2 • Q = 0) :
    Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛₀ ≅ 𝓛₀) := by sorry
