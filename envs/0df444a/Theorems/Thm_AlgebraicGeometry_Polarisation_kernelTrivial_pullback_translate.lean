-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_pullback_translate
-- name    : AlgebraicGeometry.Polarisation.kernelTrivial_pullback_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/76daa1ff-2cf8-5593-865a-28e261d4b1ac
-- title:
--   Triviality of K(L) is translation-invariant
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: a rule assigning to each test scheme $T$ with structure morphism $t : T \to \operatorname{Spec} k$ a multiplication, unit and inverse on the set of $T$-points `SchemeHomOver t f` (morphisms $T \to A$ over $t$), satisfying associativity, the unit laws, left inversion, and naturality of multiplication under change of test scheme. Assume $L$ is commutative, that $f$ carries an `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre of the underlying map of $f$ over a point of $\operatorname{Spec} k$ is connected, and $f$ admits some relative group law, and let $\mathcal L$ be a module on $A$ which is invertible, i.e. locally on $A$ its restriction is isomorphic to the unit sheaf. Suppose $\mathcal L$ satisfies `KernelTrivial f L`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every $T$-point $x'$ of $A$ over $t$, if the pullback along the slice map $\operatorname{Spec} R \times_{\operatorname{Spec} k} A \to A \times_{\operatorname{Spec} k} A$ determined by $x'$ of the Mumford bundle $m^*\mathcal L \otimes \operatorname{pr}_1^*\mathcal L^\vee \otimes \operatorname{pr}_2^*\mathcal L^\vee$ is isomorphic to the monoidal unit locally over the base, i.e. over the preimage of some open neighbourhood of each point of $\operatorname{Spec} R$, then $x'$ is the unit point of $L$ over $t$. Then for every $k$-point $x$ of $A$ (a section of $f$ over the identity of $\operatorname{Spec} k$), the pullback of $\mathcal L$ along the translation endomorphism $\operatorname{translate}$ given by $L$-multiplication by $x$ also satisfies `KernelTrivial f L`.
--
--   This is the translation-invariance of the functorial kernel $K(\mathcal L)$ of an invertible sheaf on an abelian scheme: if $K(\mathcal L)$ is trivial then so is $K(T_x^*\mathcal L)$, because $T_x^*\mathcal L$ differs from $\mathcal L$ by a class in $\operatorname{Pic}^0$, whose Mumford bundle is trivial. It feeds the symmetrisation step [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isSymmetric_kernelTrivial_locIsoOnBase_of_kernelTrivial_of_isAlgClosed`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_isSymmetric_kernelTrivial_locIsoOnBase_of_kernelTrivial_of_isAlgClosed), where a principal bundle is replaced by a symmetric translate with the same kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelTrivial_pullback_translate.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

theorem AlgebraicGeometry.Polarisation.kernelTrivial_pullback_translate
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (hK : KernelTrivial f L 𝓛) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    KernelTrivial f L ((Scheme.Modules.pullback (L.translate x)).obj 𝓛) := by sorry
