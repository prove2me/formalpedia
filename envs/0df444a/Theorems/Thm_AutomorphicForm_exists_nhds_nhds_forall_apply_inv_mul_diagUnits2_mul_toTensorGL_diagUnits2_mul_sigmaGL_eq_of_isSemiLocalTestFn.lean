-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_nhds_forall_apply_inv_mul_diagUnits2_mul_toTensorGL_diagUnits2_mul_sigmaGL_eq_of_isSemiLocalTestFn
-- name    : AutomorphicForm.exists_nhds_nhds_forall_apply_inv_mul_diagUnits2_mul_toTensorGL_diagUnits2_mul_sigmaGL_eq_of_isSemiLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/9f874702-3bdd-5a30-8211-f39b8bfca14a
-- title:
--   Small diagonal shifts fix the σ-twisted integrand
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite extension of $K$ (via a fixed $K$-algebra structure), let $\sigma$ be a $K$-algebra automorphism of $L$, and let $v$ be a nonzero prime of $\mathcal{O}_K$, with completion $K_v$ and $E := L \otimes_K K_v$. Let $\varphi : \mathrm{GL}_2(E) \to \mathbb{C}$ be a semi-local test function, i.e. $\varphi$ is locally constant and has compact support, and let $a_0, b_0 \in K_v^{\times}$ with $a_0 \neq b_0$. Then there exist a neighbourhood $U$ of $(a_0,b_0)$ and a neighbourhood $D$ of $(1,1)$ in $K_v^{\times} \times K_v^{\times}$ with the following property: for every $(a,b) \in U$, every $(d_1,d_2) \in D$ and all $\alpha, \beta \in E^{\times}$ such that the norm string of $\delta := \mathrm{diag}(\alpha,\beta)$, namely the ordered product $\prod_{i=0}^{[L:K]-1} \sigma_{\mathrm{GL}}^{i}(\delta)$ where $\sigma_{\mathrm{GL}}$ is the map induced on $\mathrm{GL}_2(E)$ by $\sigma \otimes \mathrm{id}_{K_v}$, equals the image of $\mathrm{diag}(a,b) \in \mathrm{GL}_2(K_v)$ under the map induced by $K_v \to E$, $c \mapsto 1 \otimes c$, one has, for every $x \in \mathrm{GL}_2(E)$, $$\varphi\big(x^{-1}\,\delta\,\mathrm{diag}(d_1,d_2)\,\sigma_{\mathrm{GL}}(x)\big) = \varphi\big(x^{-1}\,\delta\,\sigma_{\mathrm{GL}}(x)\big),$$ the shift $\mathrm{diag}(d_1,d_2)$ again being taken in $\mathrm{GL}_2(E)$ through $1 \otimes (-)$. Here $\mathrm{diag}(x,y)$ denotes the element of $\mathrm{GL}_2$ with matrix $!![x,0;0,y]$ and inverse $!![x^{-1},0;0,y^{-1}]$.
--
--   This is a uniform invariance statement for the integrand of a $\sigma$-twisted conjugation orbital integral on $\mathrm{GL}_2(L \otimes_K K_v)$: for a regular split target norm $(a_0,b_0)$, $a_0 \neq b_0$, a sufficiently small diagonal shift coming from $K_v^{\times} \times K_v^{\times}$ changes nothing pointwise, simultaneously for all diagonal lifts of all nearby norms. It serves as the local analytic input to [`AutomorphicForm.exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn`](thm.html#AutomorphicForm.exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn), in the comparison of twisted orbital integrals underlying base change for $\mathrm{GL}(2)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_nhds_forall_apply_inv_mul_diagUnits2_mul_toTensorGL_diagUnits2_mul_sigmaGL_eq_of_isSemiLocalTestFn.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_nhds_forall_apply_inv_mul_diagUnits2_mul_toTensorGL_diagUnits2_mul_sigmaGL_eq_of_isSemiLocalTestFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (a₀ b₀ : (v.adicCompletion K)ˣ) (hab : a₀ ≠ b₀) :
    ∃ U ∈ nhds (a₀, b₀), ∃ D ∈ nhds ((1 : (v.adicCompletion K)ˣ), (1 : (v.adicCompletion K)ˣ)),
      ∀ ab : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, ab ∈ U →
      ∀ d : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, d ∈ D →
      ∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 ab.1 ab.2) →
        ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          φ (x⁻¹ * (diagUnits2 α β * AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 d.1 d.2)) *
              AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) =
            φ (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) := by sorry
