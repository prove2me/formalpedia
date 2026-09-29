-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal
-- name    : AutomorphicForm.CuspidalSpectrum.exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/dae08db9-80f3-5cc1-9888-5f1c67dd1eb3
-- title:
--   Carrier approximation by typed level-N vectors in a cuspidal subrepresentation
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,\kappa$ be reals and $T$ a finite subset of $\mathrm{GL}_2$ of the adeles of $F$, with $d_1<d_2$, $1\le\kappa$, $0<c$, $0<d_1$, and assume the union $W^{a}=\bigcup_{x\in T}(\,\cdot\,x)$-translates of the ample centre-cut Siegel set $\mathrm{centreCutSiegelSetAmple}\,F\,c\,u\,d_1\,d_2\,\kappa$ covers modulo centre: every $g$ can be written with $\gamma g z$ in that union for some $\gamma\in\mathrm{GL}_2(F)$ and some idele unit $z$ acting by central scalars. Let $\xi$ be a homomorphism from the full group of idele units to $\mathbb{C}^\times$ with $\|\xi(z)\|=\|z\|^{\sigma}$ for the idele norm, and let $\Phi_0$ be a slab fundamental domain for the parameters $\alpha<\beta$: $0<\alpha$, $\Phi_0$ lies in the locus where the idele norm of the determinant is in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the group of global points acting on adelic Haar measure restricted to that locus. Let $N\neq\bot$ be an ideal of $\mathcal{O}_F$ and $\mathrm{tys}$ an archimedean type family. Write $P$ for the pins with carrier the analogous union $W$ of translates of the plain centre-cut Siegel set, level family $N\mapsto\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}\,F$, Hecke generators $v\mapsto\mathrm{heckeGen}\,v$ and box $\mathrm{adelicBox}\,F$, and $P^{a}$ for the same pins with $W$ replaced by $W^{a}$. Let $V$ be a $\mathbb{C}$-submodule of functions which is a cuspidal subrepresentation at $P$ (contained in the span of continuous functions all of whose right translates are smooth cuspidal automorphic at $P$ and which lie in some archimedean typed cut, and stable under right translation by the finite-adelic subgroup, by the archimedean row-isometry subgroups, and under right convolution by factorizable, archimedean bi-finite test functions), and let $\varphi_1\in V$. Let $\varphi$ be smooth cuspidal automorphic at $P^{a}$ with character $\xi$, continuous, invariant under right multiplication by $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}\,F$, and in the typed cut $\mathrm{archCutSubmodule}\,F\,\mathrm{tys}$, and suppose that for every $\varepsilon>0$ in $[0,\infty]$ there are a finite set $s$ and coefficients $l$ with $\int_{W^{a}}\|\varphi(y)-\sum_{h\in s}l(h)\varphi_1(yh)\|^{2}\,d\mu<\varepsilon$ for adelic Haar measure. Then for every $\delta>0$: $\varphi$ is a cuspidal member at $\Phi_0$, that is, smooth cuspidal automorphic at $\mathrm{fdPins}\,F\,\Phi_0$ with character $\xi$ and continuous; and there is an $x$ lying in $V$, in the same level-$N$ invariant submodule and in $\mathrm{archCutSubmodule}\,F\,\mathrm{tys}$, itself a cuspidal member at $\Phi_0$, with $\|\mathrm{toCuspSubcarrier}\,F\,h_{\Phi_0}\,\sigma\,\xi(\varphi)-\mathrm{toCuspSubcarrier}\,F\,h_{\Phi_0}\,\sigma\,\xi(x)\|<\delta$, the norm being taken in the closure inside the weighted $L^2$ carrier of the image of the cuspidal members.
--
--   This is the analytic step converting mean-square approximation over the ample covering window by finitely many right translates of a single vector of a cuspidal subrepresentation into approximation in the cuspidal subcarrier attached to the slab fundamental domain $\Phi_0$, with the level taken to be the principal congruence subgroup attached to $N$. It is used in the proof that a function approximable in this way belongs to the typed level-$N$ part of the cuspidal constituent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (φ₁ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₁ : φ₁ ∈ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hφc : Continuous φ)
    (hφN : φ ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N)
    (hφt : φ ∈ archCutSubmodule F tys)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ,
            (‖φ y - ∑ h ∈ s, l h * φ₁ (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ,
    ∃ x ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys,
    ∃ hxm : x ∈ cuspMemberSubmodule F Φ₀ ξ,
      ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩‖ < δ := by sorry
