-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample
-- name    : AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/5c06a19f-4872-5cbb-b5b9-1cbf603761e7
-- title:
--   Slab square mass dominated by ample Siegel window mass
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,\kappa$ be real numbers with $d_1<d_2$ and $1\le\kappa$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$ (the general linear group of degree $2$ over the adele ring of $F$). Write $W=\bigcup_{x\in T}\,\{g x: g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSetAmple F c u d₁ d₂ κ` consists of those $g$ lying in the centre-cut Siegel set `centreCutSiegelSet F c u d₁ d₂` (finite part integral; at every infinite place $w$ the local height $\|\det\|/\mathrm{rowNormSq}$ of the archimedean component is at least $c$, the $x$-window square is at most $u^2$, and the archimedean determinant norm lies in $[d_1,d_2]$) and satisfying in addition that the local heights at any two infinite places $w,w'$ satisfy $\mathrm{ht}_w(g)\le\kappa\,\mathrm{ht}_{w'}(g)$. Assume $W$ covers modulo the centre: for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in W$, where $\gamma$ acts through the adelic embedding and $z$ through the central scalar embedding. Let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$, let $\alpha,\beta$ be reals, and let $\Phi_0$ be a slab fundamental domain: $0<\alpha<\beta$, $\Phi_0$ is contained in the slab $\{g:\|\det g\|_{\mathbb{A}}\in[\alpha,\beta]\}$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on the adelic Haar measure restricted to that slab. Then there is a real constant $C$ such that for every continuous $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is left invariant under $\mathrm{GL}_2(F)$ and transforms by $\xi$ under central scalars, the lower Lebesgue integral of $\|\varphi\|^2$ over $\Phi_0$ is at most $C$ times the lower Lebesgue integral of $\|\varphi\|^2$ over $W$, both with respect to `adelicGLHaar (Fin 2) (𝓞 F) F`.
--
--   This is the comparison step that transfers $L^2$ mass from an exact fundamental domain inside a determinant-norm slab to a finite union of right translates of an ample centre-cut Siegel window, with a constant independent of the function. It feeds the approximation arguments for elements of the cuspidal spectrum carrier, where smallness of the integral over the Siegel window is converted into smallness of the Petersson-type norm over the slab fundamental domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple

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

theorem AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hκ : 1 ≤ κ)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) :
    ∃ C : ℝ, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, IsLsXiFunction (𝓞 F) F ⊤ ξ φ → Continuous φ →
      ∫⁻ x in Φ₀, (‖φ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        ≤ ENNReal.ofReal C *
          ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ, (‖φ x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by sorry
