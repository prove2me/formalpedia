-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_pullback_oneProdNsmul_iso_mumfordBundle_of_forall_torsion
-- name    : AlgebraicGeometry.RiemannForm.exists_pullback_oneProdNsmul_iso_mumfordBundle_of_forall_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/b724ea48-b672-51eb-a1d8-fc4369d283a0
-- title:
--   Descent of the Mumford bundle along 1×[ℓ]
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$ (a functorial group structure on the sets of $T$-points of $f$ over $\operatorname{Spec} k$, compatible with base change) that is commutative; assume the bundle of properties `AbelianSchemePropertyBundle` for $f$, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and a relative group law exists. Let $\mathcal L$ be a module on $A$ that is invertible in the sense that every point of $A$ has an open neighbourhood on which $\mathcal L$ pulls back to the unit module, let $g$ be a natural number such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and let $\ell$ be a prime that is nonzero in $k$. Assume that for every $k$-point $Q$ of the group law with $\ell Q = 0$ the pullback of $\mathcal L$ along the translation morphism $\mathrm{id} \cdot Q : A \to A$ is isomorphic to $\mathcal L$. Then there is an invertible module $\mathcal P$ on $A \times_{\operatorname{Spec} k} A$ such that: the pullback of $\mathcal P$ along the morphism $(\mathrm{pr}_1, [\ell]\circ \mathrm{pr}_2)$ (the lift of $\mathrm{pr}_1$ and $\mathrm{pr}_2$ followed by the $\ell$-fold multiplication morphism `schemeNsmul`) is isomorphic to the Mumford bundle $\Lambda(\mathcal L) = m^*\mathcal L \otimes (\mathrm{pr}_1^*\mathcal L^\vee \otimes \mathrm{pr}_2^*\mathcal L^\vee)$; and the pullbacks of $\mathcal P$ along the slice at the zero $k$-point, and of the image of $\mathcal P$ under the pullback along the symmetry of $A \times_{\operatorname{Spec} k} A$ along that same slice, are each isomorphic to the unit module. The last two clauses express bi-rigidification of $\mathcal P$ along $A \times \{e\}$ and $\{e\} \times A$.
--
--   This is the descent step in the construction of the Weil pairing from a polarisation: when all $\ell$-torsion $k$-points lie in $K(\mathcal L)$, the Mumford bundle $\Lambda(\mathcal L)$ factors through $1 \times [\ell]$, yielding a bi-rigidified line bundle on $A \times A$. It feeds the subsequent comparison of tensor powers used in the Riemann form construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_exists_pullback_oneProdNsmul_iso_mumfordBundle_of_forall_torsion.lean

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

theorem AlgebraicGeometry.RiemannForm.exists_pullback_oneProdNsmul_iso_mumfordBundle_of_forall_torsion
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (hK : ∀ Q : L.AlgPoints hc k, ℓ • Q = 0 →
      Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛)) :
    ∃ 𝓟 : (pullback f f).Modules, Scheme.Modules.IsInvertible 𝓟 ∧
      Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
          (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition))).obj 𝓟 ≅
        mumfordBundle f L 𝓛) ∧
      Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟 ≅ 𝟙_ _) ∧
      Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟) ≅ 𝟙_ _) := by sorry
