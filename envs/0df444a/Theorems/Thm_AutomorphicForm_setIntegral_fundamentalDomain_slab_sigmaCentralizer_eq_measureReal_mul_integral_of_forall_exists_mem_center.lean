-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center
-- name    : AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/97194181-f8b1-5a5a-8ae9-64d303d2e50f
-- title:
--   Twisted slab identity for one twisted class in GL₂
-- statement:
--   Let $L$ be a number field, $\mathbb{A}_L$ its adele ring and $G=\mathrm{GL}_2(\mathbb{A}_L)$ with its Borel structure; let $\mu$ be an s-finite left-invariant measure on $G$. Let $\sigma\colon L\to L$ be a ring homomorphism and $\sigma_{\mathbb A}\colon G\to G$ a continuous group endomorphism with $\sigma_{\mathbb A}(\iota\gamma)=\iota(\sigma\gamma)$ for all $\gamma\in\mathrm{GL}_2(L)$, where $\iota$ is the map $\mathrm{GL}_2(L)\to G$ induced by $L\to\mathbb{A}_L$ and $\sigma$ acts entrywise. Fix $\delta_0\in\mathrm{GL}_2(L)$, put $\delta=\iota\delta_0$, and let $T'=\{t\in G: t\,\delta\,\sigma_{\mathbb A}(t)^{-1}=\delta\}$, a subgroup with its Borel structure and an s-finite right-invariant measure $\tau'$; assume that for every real $c>0$ some $t$ in the centre of $T'$ has $\|\det t\|=c$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character of $\mathbb{A}_L$. Let $\Gamma=\{\gamma\in\mathrm{GL}_2(L):\gamma\,\delta_0\,\sigma(\gamma)^{-1}=\delta_0\}$, let $\alpha,\beta\in\mathbb{R}$ with $\alpha>0$ and $B=\{g:\|\det g\|\in[\alpha,\beta]\}$. Suppose $\Psi\subseteq G$ is a fundamental domain for $\iota(\Gamma)$ acting on $\mu|_B$, and $D'\subseteq T'$ a fundamental domain for the right action of $\iota(\Gamma)\cap T'$, viewed as a subgroup of $T'$, on $\tau'$. Let $\varphi\colon G\to\mathbb{C}$ be measurable and $w\colon G\to\mathbb{R}$ measurable, non-negative and of compact support, with $\int_{T'}w(tx)\,d\tau'(t)=1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma_{\mathbb A}(x))\neq 0$. Then $$\int_{\Psi}\varphi\bigl(x^{-1}\delta\,\sigma_{\mathbb A}(x)\bigr)\,d\mu|_B(x)=\tau'\bigl(D'\cap\{t:\|\det t\|\in[\alpha,\beta]\}\bigr)\cdot\int_G\varphi\bigl(x^{-1}\delta\,\sigma_{\mathbb A}(x)\bigr)w(x)\,d\mu(x),$$ the covolume being the real-valued measure of the indicated set, coerced into $\mathbb{C}$.
--
--   This is the per-class form of a $\sigma$-twisted elliptic term: the contribution of the twisted class of $\delta_0$ over a determinant slab is the slab covolume of $\Gamma\backslash T'$ times the global twisted orbital integral, the latter expressed through the weight $w$ rather than a quotient measure. It is obtained from the general slab quotient identity [`AutomorphicForm.setIntegral_fundamentalDomain_slab_eq_measureReal_smul_integral_of_forall_integral_eq_one`](thm.html#AutomorphicForm.setIntegral_fundamentalDomain_slab_eq_measureReal_smul_integral_of_forall_integral_eq_one) applied with $T=T'$ and $\Gamma$ the rational twisted centraliser, and it feeds the twisted adelic-action version of the identity and the subsequent summation over norm classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center
    (L : Type) [Field L] [NumberField L]
    (μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 L) L)) [SFinite μ] [μ.IsMulLeftInvariant]
    (σ : L →+* L) (σA : AutomorphicForm.AdelicGL2 (𝓞 L) L →* AutomorphicForm.AdelicGL2 (𝓞 L) L)
    (hσA : ∀ γ : GL (Fin 2) L, σA (AutomorphicForm.globalPoints (𝓞 L) L γ) =
      AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map σ γ))
    (hσAc : Continuous σA)
    (δ₀ : GL (Fin 2) L)
    [MeasurableSpace (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀))]
    [BorelSpace (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀))]
    (τ' : Measure (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀)))
    [SFinite τ'] [τ'.IsMulRightInvariant]
    (hT' : ∀ c : ℝ, 0 < c →
      ∃ t : AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀),
        t ∈ Subgroup.center
            (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀)) ∧
          NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 L) L)) = c)
    (α β : ℝ) (hα : 0 < α)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨ : IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map σ) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) Ψ
      (μ.restrict {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (D' : Set (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀)))
    (hD' : IsFundamentalDomain
      (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map σ) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf
        (AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀))).op D' τ')
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφm : Measurable φ)
    (w : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w)
    (hwc : HasCompactSupport w)
    (hw1 : ∀ x, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * σA x) ≠ 0 →
      ∫ t : AutomorphicForm.sigmaCentralizer σA (AutomorphicForm.globalPoints (𝓞 L) L δ₀),
        w ((t : AutomorphicForm.AdelicGL2 (𝓞 L) L) * x) ∂τ' = 1) :
    ∫ x in Ψ, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * σA x)
        ∂(μ.restrict {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈
          Set.Icc α β}) =
      (τ'.real (D' ∩ {t | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det
        (t : AutomorphicForm.AdelicGL2 (𝓞 L) L)) ∈ Set.Icc α β}) : ℂ) *
        ∫ x, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * σA x) * (w x : ℂ) ∂μ := by sorry
