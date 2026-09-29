-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle
-- name    : AlgebraicGeometry.RiemannForm.exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/fc0f24d7-a24a-5fa0-b7e4-a52b5b8b4794
-- title:
--   Bi-rigidified descent of the Mumford bundle along 1×[ℓ]
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme with a morphism $f : A \to \operatorname{Spec} k$, and $L$ a relative group law for $f$: a group structure, natural in $T$, on the sets of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$ for morphisms $t : T \to \operatorname{Spec} k$. Assume $L$ is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with $\mathcal L|_U$ isomorphic to the unit sheaf of modules, let $\ell \in \mathbb N$, and let $\mathcal P$ be an invertible module on $A\times_k A$ such that the pullback of $\mathcal P$ along $(p_1, [\ell]\circ p_2) : A\times_k A \to A\times_k A$, where $[\ell]$ is the morphism obtained by $\ell$-fold multiplication of the identity point under $L$, is isomorphic to the Mumford bundle $\Lambda(\mathcal L) = m^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$, $m$ being the addition morphism of $L$. Then there exists an invertible module $\mathcal P'$ on $A\times_k A$ with the same property, namely $(p_1,[\ell]\circ p_2)^*\mathcal P' \cong \Lambda(\mathcal L)$, and in addition both rigidifications: the pullback of $\mathcal P'$ along the slice $(p_1, e\circ p_2) : A\times_k \operatorname{Spec} k \to A \times_k A$ at the zero element $e$ of the group of $k$-points of $L$ is isomorphic to the unit object, and likewise for the pullback of the swap $(\text{pullbackSymmetry})^*\mathcal P'$ along that same slice.
--
--   This is the bi-rigidification step for line bundles on $A\times_k A$: a bundle descending the Mumford bundle along $1\times[\ell]$ may be corrected, by tensoring with a pullback from the second factor, so as to be trivial on both $A\times\{e\}$ and $\{e\}\times A$. It feeds the construction of the Riemann (Weil) form attached to a polarisation, being used in the passage from vanishing on torsion points to a bundle on $A\times_k A$ pulling back to the Mumford bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle.lean

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

theorem AlgebraicGeometry.RiemannForm.exists_birigidified_pullback_oneProdNsmul_iso_mumfordBundle_of_pullback_oneProdNsmul_iso_mumfordBundle
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ)
    (𝓟 : (pullback f f).Modules) (h𝓟 : Scheme.Modules.IsInvertible 𝓟)
    (h : Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
          (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition))).obj 𝓟 ≅
        mumfordBundle f L 𝓛)) :
    ∃ 𝓟' : (pullback f f).Modules, Scheme.Modules.IsInvertible 𝓟' ∧
      Nonempty ((Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ L.schemeNsmul ℓ)
          (by rw [Category.assoc, RelativeGroupLaw.schemeNsmul_over]; exact pullback.condition))).obj 𝓟' ≅
        mumfordBundle f L 𝓛) ∧
      Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj 𝓟' ≅ 𝟙_ _) ∧
      Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓟') ≅ 𝟙_ _) := by sorry
