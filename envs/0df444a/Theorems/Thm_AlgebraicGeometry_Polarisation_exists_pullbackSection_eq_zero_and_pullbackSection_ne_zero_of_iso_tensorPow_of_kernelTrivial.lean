-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_pullbackSection_eq_zero_and_pullbackSection_ne_zero_of_iso_tensorPow_of_kernelTrivial
-- name    : AlgebraicGeometry.Polarisation.exists_pullbackSection_eq_zero_and_pullbackSection_ne_zero_of_iso_tensorPow_of_kernelTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/5bba2d30-eb55-5180-bd38-423eb066e4d2
-- title:
--   Tangent vectors separated by sections of mathcal L₀^{⊗ n}, n≥4
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$, equipped with a relative group law $L$ (a functorial group structure on the sections of $f$ over every test scheme) which is commutative, and assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, each fibre of the underlying map is connected, and a relative group law exists. Let $\mathcal L_0$ be an $A$-module which is invertible (locally on $A$ its restriction is isomorphic to the unit module), satisfying `KernelTrivial`: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every section $x$ of $f$ over $t$, if the pullback along `sliceAt f x` of the Mumford bundle $m^*\mathcal L_0 \otimes p_1^*\mathcal L_0^\vee \otimes p_2^*\mathcal L_0^\vee$ is, locally on the base $\operatorname{Spec} R$, isomorphic to the unit module, then $x$ is the identity section $L.one\,t$. Assume further that $\Gamma(\mathcal L_0,\top)$ has positive $k$-dimension, where $k$ acts through $\Gamma(A,\top)$ via $f$. Let $n \ge 4$ and let $\mathcal N$ be an $A$-module isomorphic to the $n$-fold tensor power $\mathcal L_0^{\otimes n}$. Finally let $P : \operatorname{Spec} k[\varepsilon] \to A$ be a morphism over $k$ (i.e. $P$ followed by $f$ is $\operatorname{Spec}$ of the structure map $k \to k[\varepsilon]$), and suppose $P$ differs from $\iota \circ (o \circ P)$, where $o = \operatorname{Spec}$ of the projection $k[\varepsilon] \to k$, $\varepsilon \mapsto 0$, and $\iota = \operatorname{Spec}$ of $k \to k[\varepsilon]$; that is, $P$ is not the constant $k[\varepsilon]$-point at its own reduction. Then there is a global section $s : \mathbf 1 \to \mathcal N$ whose pullback section along $o$ followed by $P$ vanishes, while its pullback section along $P$ is nonzero.
--
--   This is the tangent-vector case of the projective-embedding criterion for an ample line bundle on an abelian variety (Mumford, Abelian Varieties §17, Theorem p. 163(2)) in the situation of a bundle with trivial theta group kernel: global sections of $\mathcal L_0^{\otimes n}$ for $n \ge 4$ separate a first-order neighbourhood of a point. It feeds the construction of the projective presentation of $A$, being used in [`AlgebraicGeometry.Polarisation.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_iso_tensorPow_of_kernelTrivial_of_four_le`](thm.html#AlgebraicGeometry.Polarisation.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_iso_tensorPow_of_kernelTrivial_of_four_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_pullbackSection_eq_zero_and_pullbackSection_ne_zero_of_iso_tensorPow_of_kernelTrivial.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_pullbackSection_eq_zero_and_pullbackSection_ne_zero_of_iso_tensorPow_of_kernelTrivial
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓛₀, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓛₀, ⊤))
    (n : ℕ) (hn : 4 ≤ n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓛₀.tensorPow n)
    (P : Spec (CommRingCat.of (DualNumber k)) ⟶ A)
    (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (hP0 : P ≠ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P)) :
    ∃ s : 𝟙_ A.Modules ⟶ 𝓝,
      Scheme.Modules.pullbackSection (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P) s = 0 ∧
        Scheme.Modules.pullbackSection P s ≠ 0 := by sorry
