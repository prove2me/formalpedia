-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_oneProdNsmul_iso_tensorPow_of_birigidified
-- name    : AlgebraicGeometry.Polarisation.nonempty_pullback_oneProdNsmul_iso_tensorPow_of_birigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/e3eda7df-5820-575e-ab7e-37aa629fd8f9
-- title:
--   Bi-rigidified bundle on A× A is additive in the second variable
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme, $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over $k$-schemes $t : T \to \operatorname{Spec} k$, natural in $T$; assume $L$ is commutative. Assume the property bundle `AbelianSchemePropertyBundle` for $f$ (smooth, proper, connected fibres, and a relative group law exists) and that every fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $\mathcal{P}$ be a module on $A \times_k A =$ `pullback f f` which is invertible (locally on an open cover isomorphic to the unit module), and assume two rigidifications: the pullback of $\mathcal{P}$ along the slice $(p_1, p_2 \circ e)$ at the zero $e$ of the group of $k$-points $\mathrm{Additive}$-structure $L.\mathrm{AlgPoints}$ is isomorphic to the unit, and likewise for the pullback of $\mathcal{P}$ along the symmetry $\sigma$ of $A \times_k A$ first. Then for every $\ell \in \mathbb{N}$ there exists an isomorphism between the pullback of $\mathcal{P}$ along $\mathrm{lift}(p_1, [\ell] \circ p_2)$ and $\mathcal{P}^{\otimes \ell}$, the latter defined recursively by $\mathcal{P}^{\otimes 0} = \mathbf{1}$, $\mathcal{P}^{\otimes (n+1)} = \mathcal{P}^{\otimes n} \otimes \mathcal{P}$, where $[\ell]$ is the underlying morphism $A \to A$ of the $\ell$-fold sum of the identity section.
--
--   This is the second-variable additivity of a bi-rigidified (Poincaré-type) line bundle on $A \times A$: $(1 \times [\ell])^*\mathcal{P} \cong \mathcal{P}^{\otimes \ell}$, the multiplicative counterpart of the theorem of the cube in Mumford's treatment. It is obtained from the three-variable additivity statement [`AlgebraicGeometry.Polarisation.nonempty_pullback_addMorProd_iso_tensor_of_birigidified`](thm.html#AlgebraicGeometry.Polarisation.nonempty_pullback_addMorProd_iso_tensor_of_birigidified), and is used for the Mumford bundle attached to a line bundle and in the construction of the Riemann form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_nonempty_pullback_oneProdNsmul_iso_tensorPow_of_birigidified.lean

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

theorem AlgebraicGeometry.Polarisation.nonempty_pullback_oneProdNsmul_iso_tensorPow_of_birigidified
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _))
    (ℓ : ℕ) :
    Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
          (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition))).obj 𝓟 ≅
      𝓟.tensorPow ℓ) := by sorry
