-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_mul_comp_toProj_eq_const_dualNumber_of_forall_pullbackSection_eq_zero_imp_of_ne_zero
-- name    : AlgebraicGeometry.Polarisation.mul_comp_toProj_eq_const_dualNumber_of_forall_pullbackSection_eq_zero_imp_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/d4fe0b6e-2b2f-519e-a4a3-382abc8f48f7
-- title:
--   Projective presentation is constant on a translated tangent vector
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, and let $L$ be a relative group law on $f$, i.e. functorial group structures on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$; assume $L$ commutative and that $f$ is smooth, proper, with connected fibres and carrying a relative group law. Let $\mathcal{L}_0$ be an invertible $\mathcal{O}_A$-module, $j \le n-1$ natural numbers, and $\mathcal{N} \cong \mathcal{L}_0^{\otimes n}$. Let $\mathfrak{P}$ be a projective presentation of $\mathcal{L}_0^{\otimes j}$ over $f$ by $N+1$ global sections: sections $\sigma_i$, a morphism $\mathfrak{P}.\mathrm{toProj} : A \to \mathbb{P}^N_k$ over $\operatorname{Spec} k$, bijectivity of multiplication by $\sigma_i$ on opens inside the $i$-th basic open, and the ratio compatibility $(X_j/X_i)\cdot\sigma_i = \sigma_j$ there. Let $P$ be a $k[\varepsilon]$-point of $A$ over $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$, and $a$ a $k$-point with $a$ equal to the closed-point inclusion $\operatorname{Spec} k \to \operatorname{Spec} k[\varepsilon]$ (induced by $k[\varepsilon] \to k$) followed by $P$. Assume that every global section $s : \mathbb{1} \to \mathcal{N}$ whose pullback along $a$ vanishes has vanishing pullback along $P$. Let $\theta$ be a global section of $\mathcal{L}_0$, let $x, u$ be $k$-points, and let $x_\varepsilon$ be the $k[\varepsilon]$-point obtained from $x$ by composing with $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$. Assume the pullbacks of $\theta$ along the $k$-points $a\cdot u$ and $a\cdot x^{-j}\cdot u^{-(n-j-1)}$ (products in the group of $k$-points) are both non-zero. Then the $k[\varepsilon]$-point $x_\varepsilon \cdot P$ followed by $\mathfrak{P}.\mathrm{toProj}$ equals $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} k$ followed by the $k$-point $x \cdot a$ followed by $\mathfrak{P}.\mathrm{toProj}$.
--
--   This is the tangent-vector step in Mumford's argument that a suitable multiple of an invertible sheaf separates tangent vectors: the morphism to $\mathbb{P}^N_k$ attached to $\mathcal{L}_0^{\otimes j}$ contracts the tangent vector $x_\varepsilon\cdot P$ to the constant $k[\varepsilon]$-point at $x\cdot a$, for auxiliary $k$-points $x,u$ in general position with respect to $\theta$. It feeds the stabiliser statement [`AlgebraicGeometry.Polarisation.isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp_dualNumber`](thm.html#AlgebraicGeometry.Polarisation.isInStabilizer_tensorPow_mul_inv_of_forall_pullbackSection_eq_zero_imp_dualNumber), and is proved by combining the construction of a section of $\mathcal{N}$ as a product of translated sections with the constancy criterion [`AlgebraicGeometry.Scheme.Modules.ProjPresentation.comp_toProj_eq_const_of_forall_pullbackSection_eq_zero_imp`](thm.html#AlgebraicGeometry.Scheme.Modules.ProjPresentation.comp_toProj_eq_const_of_forall_pullbackSection_eq_zero_imp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_mul_comp_toProj_eq_const_dualNumber_of_forall_pullbackSection_eq_zero_imp_of_ne_zero.lean

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

theorem AlgebraicGeometry.Polarisation.mul_comp_toProj_eq_const_dualNumber_of_forall_pullbackSection_eq_zero_imp_of_ne_zero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛₀ : A.Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀)
    (j n : ℕ) (hjn : j + 1 ≤ n) (𝓝 : A.Modules) (e : 𝓝 ≅ 𝓛₀.tensorPow n)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation (𝓛₀.tensorPow j) f N)
    (P : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) f)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (ha : a.1 = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P.1)
    (H : ∀ s : 𝟙_ A.Modules ⟶ 𝓝,
      Scheme.Modules.pullbackSection (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P.1) s = 0 →
        Scheme.Modules.pullbackSection P.1 s = 0)
    (θ : 𝟙_ A.Modules ⟶ 𝓛₀) (x u : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (xε : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) f)
    (hxε : xε.1 = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ x.1)
    (hu : Scheme.Modules.pullbackSection
      (letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k))); a * u).1 θ ≠ 0)
    (hx : Scheme.Modules.pullbackSection
      (letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k))); a * (x ^ j)⁻¹ * (u ^ (n - j - 1))⁻¹).1 θ ≠ 0) :
    (letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))); xε * P).1 ≫ 𝔓.toProj =
      Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
        ((letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k))); x * a).1 ≫ 𝔓.toProj) := by sorry
