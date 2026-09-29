-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_tsum_comp_globalPoints_inv_mul_eq_lintegral_haarQuotient_setLIntegral_of_subgroup
-- name    : AutomorphicForm.setLIntegral_tsum_comp_globalPoints_inv_mul_eq_lintegral_haarQuotient_setLIntegral_of_subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/95f43a6b-ed3f-5f8a-afeb-492bbe88a8fe
-- title:
--   Unfolding a coset sum on Φ₀ to HbackslashGL₂(A_L)
-- statement:
--   Let $L$ be a number field and write $\iota =$ [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) for the group homomorphism $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying the algebra map $L\to\mathbb{A}_L$ entrywise, the target being $\mathrm{GL}_2$ of the adele ring of $\mathcal{O}_L\subseteq L$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`. Let $\Gamma_1\le\mathrm{GL}_2(L)$ be a subgroup, $S\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ a measurable set with $\iota(\gamma)x\in S\iff x\in S$ for all $\gamma\in\Gamma_1$ and all $x$, and $\Phi_0\subseteq S$ a fundamental domain for $\iota(\Gamma_1)$ acting on the Haar measure restricted to $S$. Let $\Lambda\le\Gamma_1$, let $\iota$ index a countable family $r:\iota\to\mathrm{GL}_2(L)$ with all $r_i\in\Gamma_1$ such that each $\gamma\in\Gamma_1$ satisfies $r_i^{-1}\gamma\in\Lambda$ for exactly one $i$. Let $H\le\mathrm{GL}_2(\mathbb{A}_L)$ be a closed subgroup containing $\iota(\Lambda)$, carrying a measure $\mu_H$ that is both a Haar measure and right invariant, and let $\Omega\subseteq H$ be a fundamental domain for $\iota(\Lambda)$ viewed as a subgroup of $H$, with respect to $\mu_H$. Finally let $f:\mathrm{GL}_2(\mathbb{A}_L)\to[0,\infty]$ be measurable with $f(\iota(\gamma)x)=f(x)$ for all $\gamma\in\Lambda$. Then $$\int^-_{\Phi_0}\sum_i f(\iota(r_i)^{-1}x)\,dx = \int^-_{q}\Big(\int^-_{\Omega}\mathbf{1}_S f\big(h\,q.\mathrm{out}\big)\,d\mu_H(h)\Big)\,dq,$$ the outer integral being over the quotient of $\mathrm{GL}_2(\mathbb{A}_L)$ by the left-multiplication orbit relation of $H$, against the measure [`HaarQuotient.measure`](def/HaarQuotient.html#L28), namely the pushforward along the quotient map of the Haar measure weighted by the density $g\mapsto w(g)/\int^-_{H} w(xg)\,d\mu_H(x)$, and $q.\mathrm{out}$ a chosen representative of the class $q$.
--
--   This is the unconditional $[0,\infty]$-valued (Tonelli) form of the unfolding step in the theory of automorphic forms on $\mathrm{GL}_2$ over a number field: a sum over coset representatives of $\Lambda$ in $\Gamma_1$, integrated over a fundamental domain for $\Gamma_1$, is rewritten as an iterated integral over $H\backslash\mathrm{GL}_2(\mathbb{A}_L)$ of an integral over a fundamental domain in the adelic group $H$. It serves to discharge the absolute-convergence hypothesis of the corresponding Bochner-integral statement, and is cited by [`AutomorphicForm.setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn`](thm.html#AutomorphicForm.setLIntegral_tsum_norm_bracket_mul_twistedOrbital_lt_top_and_integrableOn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_tsum_comp_globalPoints_inv_mul_eq_lintegral_haarQuotient_setLIntegral_of_subgroup.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_HaarQuotient
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain
open scoped Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setLIntegral_tsum_comp_globalPoints_inv_mul_eq_lintegral_haarQuotient_setLIntegral_of_subgroup
    (L : Type) [Field L] [NumberField L]
    (Γ₁ : Subgroup (GL (Fin 2) L))
    (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hSm : MeasurableSet S)
    (hS : ∀ γ ∈ Γ₁, ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      AutomorphicForm.globalPoints (𝓞 L) L γ * x ∈ S ↔ x ∈ S)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hΦ₀S : Φ₀ ⊆ S)
    (hΦ₀ : IsFundamentalDomain (Γ₁.map (AutomorphicForm.globalPoints (𝓞 L) L)) Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S))

    (Λ : Subgroup (GL (Fin 2) L)) (hΛΓ : Λ ≤ Γ₁) {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L)
    (hrΓ : ∀ i, r i ∈ Γ₁) (hr : ∀ γ ∈ Γ₁, ∃! i, (r i)⁻¹ * γ ∈ Λ)

    (H : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hH : IsClosed (H : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)))
    (hΛH : Λ.map (AutomorphicForm.globalPoints (𝓞 L) L) ≤ H)
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Ω : Set H) (hΩ : IsFundamentalDomain ((Λ.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH)
    (f : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℝ≥0∞) (hf : Measurable f)
    (hfΛ : ∀ γ ∈ Λ, ∀ x, f (AutomorphicForm.globalPoints (𝓞 L) L γ * x) = f x) :
    ∫⁻ x in Φ₀, ∑' i, f ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∫⁻ q, (∫⁻ h in Ω, S.indicator f ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH)
        ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by sorry
