-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_mul_comp_toProj_eq_mul_comp_toProj_of_forall_pullbackSection_eq_zero_imp_of_ne_zero
-- name    : AlgebraicGeometry.Polarisation.mul_comp_toProj_eq_mul_comp_toProj_of_forall_pullbackSection_eq_zero_imp_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/77af5475-6df0-5ca4-8772-f00a6df872fb
-- title:
--   Agreement of projective presentation at translated k-points
-- statement:
--   Let $k$ be an algebraically closed field and $f : A \to \operatorname{Spec} k$ a morphism of schemes, equipped with a relative group law $L$ on $f$, i.e. a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ t = t\}$ of $T$-points over $\operatorname{Spec} k$, natural in $T$; assume $L$ is commutative, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, every fibre of $f$ is connected, and a relative group law exists. Let $\mathcal L_0$ be an $A$-module which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ with the restriction of $\mathcal L_0$ to $U$ isomorphic to the unit module, let $j, n$ be natural numbers with $j + 1 \le n$, and let $\mathcal N$ be an $A$-module with an isomorphism $\mathcal N \cong \mathcal L_0^{\otimes n}$ (iterated tensor power, with $\mathcal L_0^{\otimes 0}$ the unit). Let $\mathfrak P$ be a projective presentation of $\mathcal L_0^{\otimes j}$ over $f$ of dimension $N$: global sections $\sigma_0,\dots,\sigma_N$ of $\mathcal L_0^{\otimes j}$ together with a morphism $\mathfrak P.\mathrm{toProj} : A \to \operatorname{Proj}$ of the homogeneous coordinate algebra in $N+1$ variables over $k$, lying over $f$, such that on the preimage of each basic open $\{X_i \ne 0\}$ multiplication by $\sigma_i$ is bijective from functions to sections, and the pullbacks of the ratios $X_j/X_i$ carry $\sigma_i$ to $\sigma_j$. Let $a, b$ be $k$-points of $A$ over the identity of $\operatorname{Spec} k$ such that every global section $s$ of $\mathcal N$ (a morphism from the unit module) whose pullback along $a$ vanishes also has vanishing pullback along $b$. Let $\theta$ be a global section of $\mathcal L_0$ and $x, u$ further such $k$-points, and suppose that the pullbacks of $\theta$ along $b\cdot u$ and along $b\cdot (x^{j})^{-1}\cdot (u^{\,n-j-1})^{-1}$ are both non-zero, products and inverses taken in the group of $k$-points given by $L$. Then $\mathfrak P.\mathrm{toProj} \circ (a\cdot x) = \mathfrak P.\mathrm{toProj} \circ (b\cdot x)$.
--
--   This is the point-theoretic core of Mumford's argument that, when the complete linear system of $\mathcal L_0^{\otimes n}$ fails to separate $a$ from $b$, the morphism to projective space defined by sections of $\mathcal L_0^{\otimes j}$ cannot distinguish the translates $a\cdot x$ and $b\cdot x$ either, for auxiliary points $x, u$ in general position with respect to $\theta$. It feeds the stabiliser statement [`AlgebraicGeometry.Polarisation.isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp`](thm.html#AlgebraicGeometry.Polarisation.isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp) in the analysis of polarisations on the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_mul_comp_toProj_eq_mul_comp_toProj_of_forall_pullbackSection_eq_zero_imp_of_ne_zero.lean

import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Polarisation.mul_comp_toProj_eq_mul_comp_toProj_of_forall_pullbackSection_eq_zero_imp_of_ne_zero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (j n : ℕ) (hjn : j + 1 ≤ n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓛₀.tensorPow n)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation (𝓛₀.tensorPow j) f N)
    (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (H : ∀ s : 𝟙_ A.Modules ⟶ 𝓝,
      Scheme.Modules.pullbackSection a.1 s = 0 → Scheme.Modules.pullbackSection b.1 s = 0)
    (θ : 𝟙_ A.Modules ⟶ 𝓛₀) (x u : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hu : Scheme.Modules.pullbackSection
      (letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k))); b * u).1 θ ≠ 0)
    (hx : Scheme.Modules.pullbackSection
      (letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k))); b * (x ^ j)⁻¹ * (u ^ (n - j - 1))⁻¹).1 θ ≠ 0) :
    (letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k))); a * x).1 ≫ 𝔓.toProj =
      (letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k))); b * x).1 ≫ 𝔓.toProj := by sorry
