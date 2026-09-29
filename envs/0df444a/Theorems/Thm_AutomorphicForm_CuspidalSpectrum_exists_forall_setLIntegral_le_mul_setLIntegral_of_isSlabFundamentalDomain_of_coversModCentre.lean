-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre
-- name    : AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/fd8e4ec2-a3ad-58be-bdb8-19056ef4b71c
-- title:
--   Square mass on a slab fundamental domain dominated by a covering Siegel window
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $W=\bigcup_{x\in T}S\cdot x$ for the union of the right translates by $x\in T$ of the centre-cut Siegel set $S=$ `centreCutSiegelSet F c u d₁ d₂`, consisting of those $g$ whose finite component lies in the full-level integral subgroup `finiteIntegralGL2` and which satisfy, at every infinite place $w$ of $F$, $c\le\lvert\det\rvert/\mathrm{rowNormSq}$, $\mathrm{topNormSq}/\mathrm{rowNormSq}-(\lvert\det\rvert/\mathrm{rowNormSq})^2\le u^2$ and $\lVert\det\rVert_w\in[d_1,d_2]$, all formed from the $w$-component of the archimedean part of $g$. Assume $W$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ has $\gamma g z\in W$ for some $\gamma\in\mathrm{GL}_2(F)$ (via `globalPoints`) and some central scalar idele $z$. Let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$, and let $\Phi_0$ satisfy `IsSlabFundamentalDomain F α β`: $0<\alpha<\beta$, $\Phi_0$ lies in the slab where the idele norm of $\det$ belongs to $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on adelic Haar measure restricted to that slab. Then there is a real $C$ such that for every continuous $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ with $\varphi(\gamma g)=\varphi(g)$ for $\gamma\in\mathrm{GL}_2(F)$ and $\varphi(zg)=\xi(z)\varphi(g)$ for central scalar ideles $z$, the lower Lebesgue integral of $\lVert\varphi\rVert^2$ over $\Phi_0$ is at most $\mathrm{ofReal}\,C$ times the lower Lebesgue integral of $\lVert\varphi\rVert^2$ over $W$, both with respect to the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the transfer of $L^2$-mass from an exact fundamental domain inside a determinant-norm slab to a finite union of right translates of a centre-cut Siegel set that covers modulo the centre, with a constant uniform in the automorphic function. It feeds the bound [`AutomorphicForm.exists_forall_setLIntegral_iUnion_centreCutSiegelSet_le_mul_of_coversModCentre_of_forall_ncard_le`](thm.html#AutomorphicForm.exists_forall_setLIntegral_iUnion_centreCutSiegelSet_le_mul_of_coversModCentre_of_forall_ncard_le) used in the analysis of the cuspidal spectrum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

open AutomorphicForm.CuspidalSpectrum
open scoped ENNReal

theorem AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) :
    ∃ C : ℝ, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsLsXiFunction (𝓞 F) F ⊤ ξ φ → Continuous φ →
      ∫⁻ x in Φ₀, (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ ENNReal.ofReal C *
          ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂, (‖φ x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by sorry
