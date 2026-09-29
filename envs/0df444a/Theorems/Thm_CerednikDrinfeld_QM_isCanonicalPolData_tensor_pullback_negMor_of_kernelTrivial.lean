-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_isCanonicalPolData_tensor_pullback_negMor_of_kernelTrivial
-- name    : CerednikDrinfeld.QM.isCanonicalPolData_tensor_pullback_negMor_of_kernelTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/046d92f5-bba3-5d40-8a13-6a360333f32a
-- title:
--   Symmetrisation yields canonical polarisation data over an algebraically closed field
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a morphism of schemes, and let $L$ be a relative group law on $f$ (functorial multiplication, unit and inversion on $T$-points over $\operatorname{Spec} k$, satisfying the group axioms and compatible with base change) which is commutative, and assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre of the underlying map is connected, and a relative group law exists. Let $I$ be a type, $\mathrm{act} : I \to (A \to A)$ a family of endomorphisms with $\mathrm{act}\,x$ followed by $f$ equal to $f$, such that each $\mathrm{act}\,x$ acts on $T$-points as a homomorphism for $L$, and let $\star : I \to I$. Let $\mathcal L_0$ be a module on $A$ which is invertible (locally on $A$ its pullback is isomorphic to the unit sheaf), whose Mumford kernel is trivial in the sense of `KernelTrivial` (for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every point $x$ of $A$ over $t$, if the pullback of the Mumford bundle of $\mathcal L_0$ along the slice at $x$ is, locally on the base, isomorphic to the unit, then $x$ is the identity point), such that $0 < \operatorname{finrank}$ of the geometric-fibre $H^0$ of $\mathcal L_0$ over every algebraically closed field $k'$ with a ring map $k \to k'$, and such that $\mathcal L_0$ is Rosati-compatible with $\mathrm{act}$ and $\star$ (for each $b$, the two pullbacks of the Mumford bundle along $(\mathrm{id},\mathrm{act}\,b)$ and $(\mathrm{act}(\star b),\mathrm{id})$ agree locally over the base). Then $\mathcal L := \mathcal L_0 \otimes (-1)^*\mathcal L_0$ satisfies `IsCanonicalPolData` for $f$, $L$, $\mathrm{act}$, $\star$: it is invertible; it is symmetric, i.e. $(-1)^*\mathcal L$ and $\mathcal L$ are isomorphic locally over the base; its kernel satisfies `KernelIsTwoTorsion`; there exists a faithfully flat $k$-algebra $S'$ over which, for every relative group law on the base change compatible with $L$ on points, $\mathcal L$ pulls back to $\mathcal L' \otimes (-1)^*\mathcal L'$ for some invertible $\mathcal L'$ with trivial kernel, the isomorphism holding locally over the base; its geometric-fibre $H^0$ rank is positive over every algebraically closed extension; and it is Rosati-compatible with $\mathrm{act}$ and $\star$.
--
--   This is the assembly step producing canonical polarisation data from a principal bundle by symmetrisation: $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ is the square of a principal bundle, hence has kernel the $2$-torsion and is symmetric and positive. It feeds the construction of the canonical polarisation on fake elliptic curves, being cited in the production of kernel-trivial symmetric polarisation data after pulling back along a residue map, in the quaternionic setting of the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_isCanonicalPolData_tensor_pullback_negMor_of_kernelTrivial.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.isCanonicalPolData_tensor_pullback_negMor_of_kernelTrivial
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f)
    (act_hom : ∀ (x : I) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (star : I → I) (𝓛₀ : A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀)
    (hpos : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (sk : k →+* k'), 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛₀ k' sk)
    (hR : RosatiCompatible f L 𝓛₀ act act_over star) :
    IsCanonicalPolData f L act act_over star (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor f L)).obj 𝓛₀) := by sorry
