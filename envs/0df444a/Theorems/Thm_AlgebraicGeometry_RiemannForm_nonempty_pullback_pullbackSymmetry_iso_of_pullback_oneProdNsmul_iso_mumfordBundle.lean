-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_nonempty_pullback_pullbackSymmetry_iso_of_pullback_oneProdNsmul_iso_mumfordBundle
-- name    : AlgebraicGeometry.RiemannForm.nonempty_pullback_pullbackSymmetry_iso_of_pullback_oneProdNsmul_iso_mumfordBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/9333c00d-630b-5725-be55-21f94fd1fc9d
-- title:
--   Flip-symmetry of a bi-rigidified invertible sheaf on A× A
-- statement:
--   Let $k$ be an algebraically closed field and $f : A \to \operatorname{Spec} k$ a morphism of schemes, equipped with a relative group law $L$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over $k$-schemes $T$, compatible with base change) which is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module on $A$ which is invertible, in the sense that every point has an open neighbourhood on which the pullback of $\mathcal L$ is isomorphic to the unit; let $g$ be a natural number such that every fibre of $f$ over a point of $\operatorname{Spec} k$ has topological Krull dimension $g$; and let $\ell$ be a prime with $\ell \neq 0$ in $k$. Let $\mathcal P$ be an invertible module on $A \times_k A$ (the pullback of $f$ along itself) subject to three hypotheses: the pullback of $\mathcal P$ along the morphism $A \times_k A \to A \times_k A$ with components $\mathrm{pr}_1$ and $\mathrm{pr}_2$ followed by the $\ell$-fold multiplication endomorphism $L.\mathrm{schemeNsmul}\ \ell$ is isomorphic to the Mumford bundle $m^*\mathcal L \otimes (\mathrm{pr}_1^*\mathcal L^\vee \otimes \mathrm{pr}_2^*\mathcal L^\vee)$, where $m$ is the addition morphism attached to $L$; and the restrictions of $\mathcal P$ and of $\mathrm{flip}^*\mathcal P$ along the slice of $A \times_k A$ cut out by the zero $k$-point of $L$ are both isomorphic to the unit. Then $\mathrm{flip}^*\mathcal P$ is isomorphic to $\mathcal P$, where $\mathrm{flip}$ is the symmetry isomorphism of $A \times_k A$; all isomorphism assertions are phrased as nonemptiness of the corresponding type of isomorphisms.
--
--   This is the symmetry statement for a bi-rigidified invertible sheaf on $A \times_k A$ whose $(1 \times [\ell])$-pullback is a Mumford bundle: such a sheaf is invariant under the flip, the divisorial counterpart of the symmetry of the Riemann form attached to a polarisation. It feeds into the construction of Riemann forms, being used in the production of an isomorphism of a tensor power of such a sheaf with a tensor product under divisibility hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_nonempty_pullback_pullbackSymmetry_iso_of_pullback_oneProdNsmul_iso_mumfordBundle.lean

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

theorem AlgebraicGeometry.RiemannForm.nonempty_pullback_pullbackSymmetry_iso_of_pullback_oneProdNsmul_iso_mumfordBundle
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h₁ : Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
          (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition))).obj 𝓟 ≅ mumfordBundle f L 𝓛))
    (h₂ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _)) :
    Nonempty ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟 ≅ 𝓟) := by sorry
