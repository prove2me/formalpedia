-- Prove2me | Theorems.Thm_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat
-- name    : AutomorphicForm.isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/69608341-542d-51be-9882-b4a7deeeba6a
-- title:
--   Rapid decay on Siegel sets of a smoothed cusp vector over ℚ
-- statement:
--   Work over $F=\mathbb{Q}$, so that there is a single infinite place. Fix reals $c,u,d_1,d_2$ with $d_1<d_2$ and a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and let $D=\bigcup_{x\in T}\,(\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\;\mathbb{Q}\;c\;u\;d_1\;d_2\,]$ be the union of the right translates by the elements of $T$ of the set of $g$ whose finite part is integral, whose archimedean component has local height $\ge c$ and $x$-window square $\le u^2$ at every infinite place, and whose archimedean determinant norm lies in $[d_1,d_2]$. Assume $D$ satisfies `CoversModCentre`: every $g$ can be moved into $D$ by left multiplication by a global point of $\mathrm{GL}_2(\mathbb{Q})$ and right multiplication by a central adelic scalar. Let the pins be `productionPinsOf` for $D$, with the level subgroups $\mathrm{levelOne}\,N\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $\mathrm{heckeGen}\,v$, and the adelic box as conditioning set; their central subgroup $Z$ is all of $(\mathbb{A}_{\mathbb{Q}})^{\times}$. Let $\chi:Z\to\mathbb{C}^{\times}$ be a homomorphism with $\|\chi(z)\|=1$ for all $z$, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be continuous and satisfy the project's predicate `IsCuspAutomorphicFnAt` at these pins with character $\chi$, i.e. it is an $L(\chi)$-member at the pins' Haar data and domain $D$ (in particular transforming by $\chi$ under the centre) and is cuspidal for the unipotent subgroup with respect to the pins' conditioned additive measure. Let $f$ be a factorizable test function, i.e. $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with archimedean and finite factors satisfying the project's test-factor predicates. Then the right convolution $(\varphi*f)(g)=\int \varphi(gx) f(x)\,dx$ against adelic Haar measure is rapidly decreasing on Siegel sets: for all reals $c',u'$, every $t\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with $c'>0$ and every $N\in\mathbb{N}$ there is a constant $C$ with $\|(\varphi*f)(gt)\|\,(1+\mathrm{archHeight}(\mathrm{glArch}\,g))^{N}\le C$ for all $g$ in the integral windowed Siegel set of parameters $c',u'$.
--
--   This is the classical statement that a smoothed cusp vector decays faster than any power of the height on a Siegel set, in the adelic form needed as input to the Rankin–Selberg theory over $\mathbb{Q}$. It is used by the result asserting rapid decay of the product of such a smoothed vector with a power of the idele norm of the determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LanglandsTunnell.RankinSelberg
open AutomorphicForm

theorem AutomorphicForm.isRapidlyDecreasingOnSiegelSets_rightConv_of_isCuspAutomorphicFnAt_of_norm_apply_eq_one_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (χ : (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)).Z →* ℂˣ)
    (hχu : ∀ z, ‖((χ z : ℂˣ) : ℂ)‖ = 1)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : IsCuspAutomorphicFnAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hf : IsFactorizableTestFn ℚ f) :
    IsRapidlyDecreasingOnSiegelSets ℚ (rightConv ℚ φ f) := by sorry
