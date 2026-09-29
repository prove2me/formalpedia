-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_rosatiCompatible_of_iso_tensorPow_tensor_of_inPicZero_of_rosatiCompatible
-- name    : AlgebraicGeometry.Polarisation.rosatiCompatible_of_iso_tensorPow_tensor_of_inPicZero_of_rosatiCompatible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/d3efb04d-918f-5d48-86cb-8ee4588fa596
-- title:
--   Rosati compatibility descends to n-th roots modulo Pic⁰
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$, equipped with a relative group law $L$ (a functorial group structure on the sets of $T$-points over $\operatorname{Spec} k$, natural in $T$) which is assumed commutative, and with the bundle of properties `AbelianSchemePropertyBundle` for $f$, namely $f$ smooth and proper with connected fibres and admitting a relative group law; let $g$ be a natural number such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $I$ be a type, $\mathrm{act} : I \to (A \to A)$ a family of morphisms over $\operatorname{Spec} k$ each of which is a homomorphism for $L$ on $T$-points (composition with $\mathrm{act}\,x$ commutes with $L.\mathrm{mul}$), and $\star : I \to I$ an involution-shaped map with no further assumed properties. Let $\mathcal L, \mathcal M, P$ be $\mathcal O_A$-modules with $\mathcal L$ and $\mathcal M$ invertible (locally on $A$ isomorphic to the unit sheaf), let $P$ satisfy `InPicZero`, i.e. $P$ is invertible and for every section $x$ of $f$ over the identity of $\operatorname{Spec} k$ the pullback of $P$ along the translation $L.\mathrm{translate}\,x$ is isomorphic to $P$, and let $n > 0$ with $\mathcal L \cong \mathcal M^{\otimes n} \otimes P$. Suppose $\mathcal L$ is `RosatiCompatible` for $(\mathrm{act}, \star)$: for each $b \in I$, the pullbacks of the Mumford bundle $\Lambda(\mathcal L) = m^*\mathcal L \otimes (\mathrm{pr}_1^*\mathcal L^\vee \otimes \mathrm{pr}_2^*\mathcal L^\vee)$ on $A \times A$ along $(x,y) \mapsto (x, \mathrm{act}\,b\,y)$ and along $(x,y) \mapsto (\mathrm{act}(\star b)\,x, y)$ are locally isomorphic over the base, in the sense that every point of $\operatorname{Spec} k$ has an open neighbourhood $U$ over whose preimage the two pullbacks become isomorphic. Then $\mathcal M$ is `RosatiCompatible` for $(\mathrm{act}, \star)$ as well.
--
--   This is the statement that an $n$-th root modulo $\operatorname{Pic}^0$ of a line bundle compatible with a family of endomorphisms and an involution in the Rosati sense is itself Rosati-compatible; it rests on the multiplicativity of the Mumford bundle and its triviality for classes in $\operatorname{Pic}^0$. It is used in the quaternionic (fake elliptic curve) part of the construction, where Rosati compatibility of a candidate polarisation must be transferred from a power to the bundle itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_rosatiCompatible_of_iso_tensorPow_tensor_of_inPicZero_of_rosatiCompatible.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.rosatiCompatible_of_iso_tensorPow_tensor_of_inPicZero_of_rosatiCompatible
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act_hom : ∀ (x : I) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (star : I → I)
    (𝓛 𝓜 P : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hP : InPicZero f L P)
    (n : ℕ) (hn : 0 < n) (e : Nonempty (𝓛 ≅ 𝓜.tensorPow n ⊗ P))
    (hR : RosatiCompatible f L 𝓛 act act_over star) :
    RosatiCompatible f L 𝓜 act act_over star := by sorry
