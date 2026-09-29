-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_iso_tensorPow_of_kernelTrivial_of_four_le
-- name    : AlgebraicGeometry.Polarisation.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_iso_tensorPow_of_kernelTrivial_of_four_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/15fa3cfb-1e3d-520f-975f-46b517be1935
-- title:
--   Projective embedding separates dual-number points for n≥ 4
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets of $f$-sections over each $k$-scheme, assumed commutative (`hc`); assume further the bundle `AbelianSchemePropertyBundle`, namely that $f$ is smooth and proper, that each fibre of $f$ is connected, and that a relative group law on $f$ exists. Let $\mathcal L_0$ be a module on $A$ which is invertible, in the sense that every point of $A$ has a neighbourhood $U$ on which the restriction of $\mathcal L_0$ is isomorphic to the unit sheaf, and assume `KernelTrivial f L 𝓛₀`: for every ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} k$ and every $f$-section $x$ over $t$, if the pullback along the slice of $x$ of the Mumford bundle $m^*\mathcal L_0 \otimes p_1^*\mathcal L_0^{\vee} \otimes p_2^*\mathcal L_0^{\vee}$ is locally on the base isomorphic to the unit, then $x$ is the identity section. Assume also that $\Gamma(\mathcal L_0,\top)$ has positive finite rank as a $k$-module, for the $k$-structure coming from $f$. Let $n \ge 4$, let $\mathcal N$ be a module on $A$ with an isomorphism $\mathcal N \cong \mathcal L_0^{\otimes n}$, and let $\mathfrak P$ be a projective presentation of $\mathcal N$ over $f$ of size $N$: sections $\sigma_0,\dots,\sigma_N \in \Gamma(\mathcal N,\top)$, a morphism $\mathfrak P.\mathrm{toProj} : A \to \mathbb P^N_k$ over $\operatorname{Spec} k$, each $\sigma_i$ framing $\mathcal N$ over the preimage of the basic open $\{X_i \neq 0\}$, and the ratios $X_j/X_i$ carrying $\sigma_i$ to $\sigma_j$ there. Assume `IsSectionBasis`, i.e. $c \mapsto \sum_i c_i \cdot \sigma_i$ is a bijection from $k^{N+1}$ onto $\Gamma(\mathcal N,\top)$. Then for any two $k[\varepsilon]$-points $P, Q : \operatorname{Spec} k[\varepsilon] \to A$ lying over the structure morphism $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$, the equality $P$ followed by $\mathfrak P.\mathrm{toProj}$ equals $Q$ followed by $\mathfrak P.\mathrm{toProj}$ implies $P = Q$.
--
--   This is the separation half of the Lefschetz embedding theorem for abelian varieties, in the form that the morphism to $\mathbb P^N$ attached to a basis of $\Gamma(A,\mathcal L_0^{\otimes n})$ is injective on points with values in the dual numbers $k[\varepsilon]$ (hence separates points and tangent vectors) once the stabiliser group scheme $K(\mathcal L_0)$ is trivial and $n \ge 4$. It feeds the statement that the morphism attached to such a basis is a closed immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_iso_tensorPow_of_kernelTrivial_of_four_le.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Polarisation.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_iso_tensorPow_of_kernelTrivial_of_four_le
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hK : KernelTrivial f L 𝓛₀)
    (hpos : letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(𝓛₀, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
      0 < Module.finrank k Γ(𝓛₀, ⊤))
    (n : ℕ) (hn : 4 ≤ n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓛₀.tensorPow n)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N) (hσ : Scheme.Modules.IsSectionBasis f 𝓝 𝔓.σ)
    (P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ A)
    (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (hQ : Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (h : P ≫ 𝔓.toProj = Q ≫ 𝔓.toProj) :
    P = Q := by sorry
