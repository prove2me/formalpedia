-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
-- name    : AutomorphicForm.integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/928a10a2-e3e8-5454-84c9-623e6ac639bd
-- title:
--   Unfolding a class sum on adelic GL₂ over Hbackslash G
-- statement:
--   Let $L$ be a number field, write $G = \mathrm{GL}_2(\mathbb{A}_L)$ for the general linear group of rank $2$ over the adele ring of $L$, equipped with its Borel $\sigma$-algebra and the Haar measure $\mathrm{d}x$ given by `adelicGLHaar`, and let $\iota\colon \mathrm{GL}_2(L)\to G$ be the monoid homomorphism `globalPoints` induced by the structure map $L\to\mathbb{A}_L$ entrywise. Assume given: a measurable set $S\subseteq G$ with $\iota(\gamma)x\in S \iff x\in S$ for all $\gamma\in \mathrm{GL}_2(L)$ and $x\in G$; a subset $\Phi_0\subseteq S$ that is a fundamental domain for the left translation action of the range of $\iota$ on $G$ with respect to $\mathrm{d}x$ restricted to $S$; a subgroup $\Lambda\le \mathrm{GL}_2(L)$ together with a countable family $r\colon \iota_0\to \mathrm{GL}_2(L)$ such that every $\gamma\in \mathrm{GL}_2(L)$ satisfies $r_i^{-1}\gamma\in\Lambda$ for exactly one index $i$ (a system of representatives for the left cosets of $\Lambda$); a closed subgroup $H\le G$ containing $\iota(\Lambda)$, carrying a measure $\mu_H$ that is both a Haar measure and right invariant; a subset $\Omega\subseteq H$ that is a fundamental domain, with respect to $\mu_H$, for the subgroup of $H$ induced by $\iota(\Lambda)$; and a measurable $g\colon G\to\mathbb{C}$ with $g(\iota(\gamma)x)=g(x)$ for all $\gamma\in\Lambda$ and all $x$, subject to the finiteness assumption $\int^-_{\Phi_0}\sum_i \lVert g(\iota(r_i)^{-1}x)\rVert_{\mathrm{e}}\,\mathrm{d}x<\infty$ in $[0,\infty]$. Then: the function $x\mapsto \sum_i g(\iota(r_i)^{-1}x)$ is integrable on $\Phi_0$; for almost every $x$ with respect to $\mathrm{d}x$ restricted to $\Phi_0$ the family $i\mapsto \lVert g(\iota(r_i)^{-1}x)\rVert$ is summable; for almost every class $q$ with respect to the quotient measure [`HaarQuotient.measure`](def/HaarQuotient.html#L28), the pushforward along $G\to H\backslash G$ of $\mathrm{d}x$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25), the function $h\mapsto \mathbf 1_S(h\,q_{\mathrm{out}})\,g(h\,q_{\mathrm{out}})$ on $H$ is integrable on $\Omega$ for $\mu_H$, where $q_{\mathrm{out}}\in G$ is the chosen representative of $q$; the resulting function $q\mapsto \int_\Omega \mathbf 1_S\cdot g\,(h\,q_{\mathrm{out}})\,\mathrm{d}\mu_H(h)$ is integrable for the quotient measure; and $$\int_{\Phi_0}\sum_i g(\iota(r_i)^{-1}x)\,\mathrm{d}x \;=\; \int_{H\backslash G}\Bigl(\int_\Omega \mathbf 1_S(h\,q_{\mathrm{out}})\,g(h\,q_{\mathrm{out}})\,\mathrm{d}\mu_H(h)\Bigr)\,\mathrm{d}q.$$
--
--   This is the unfolding step of the geometric side of the trace formula for $\mathrm{GL}_2$ over a number field: a sum over a coset family $(r_i)$ integrated over a fundamental domain for $\mathrm{GL}_2(L)$ is rewritten as an integral over $H\backslash \mathrm{GL}_2(\mathbb{A}_L)$ of an orbital-type integral over a fundamental domain in the stabiliser group $H$, with the stabiliser $\Lambda$, its adelic group $H$ and the integrand $g$ kept as parameters. It is applied downstream to the bracket-weighted orbital terms and to the computation of constant terms of pseudo-Eisenstein integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral.lean

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

theorem AutomorphicForm.integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
    (L : Type) [Field L] [NumberField L]
    (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hSm : MeasurableSet S)
    (hS : ∀ (γ : GL (Fin 2) L) (x : AutomorphicForm.AdelicGL2 (𝓞 L) L),
      AutomorphicForm.globalPoints (𝓞 L) L γ * x ∈ S ↔ x ∈ S)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hΦ₀S : Φ₀ ⊆ S)
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S))

    (Λ : Subgroup (GL (Fin 2) L)) {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L)
    (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)

    (H : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hH : IsClosed (H : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)))
    (hΛH : Λ.map (AutomorphicForm.globalPoints (𝓞 L) L) ≤ H)
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Ω : Set H) (hΩ : IsFundamentalDomain ((Λ.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH)

    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hg : Measurable g)
    (hgΛ : ∀ γ ∈ Λ, ∀ x, g (AutomorphicForm.globalPoints (𝓞 L) L γ * x) = g x)
    (hfin : ∫⁻ x in Φ₀, ∑' i, ‖g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ∞) :
    IntegrableOn (fun x => ∑' i, g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) Φ₀
      (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    (∀ᵐ x ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀),
      Summable fun i => ‖g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)‖) ∧
    (∀ᵐ q ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH),
      IntegrableOn (fun h : H => S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out)) Ω μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H (AutomorphicForm.AdelicGL2 (𝓞 L) L) =>
        ∫ h in Ω, S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH)
      (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    ∫ x in Φ₀, ∑' i, g ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∫ q, (∫ h in Ω, S.indicator g ((h : AutomorphicForm.AdelicGL2 (𝓞 L) L) * q.out) ∂μH)
        ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by sorry
