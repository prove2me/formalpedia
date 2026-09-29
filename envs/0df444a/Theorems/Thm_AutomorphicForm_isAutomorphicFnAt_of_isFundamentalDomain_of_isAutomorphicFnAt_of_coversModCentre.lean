-- Prove2me | Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
-- name    : AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/3bf6045d-bfc9-544b-a9e6-ed189298c09f
-- title:
--   Automorphy transports from a Siegel window to a fundamental domain
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$ (written `AdelicGL2 (𝓞 F) F`). Put $W=\bigcup_{x\in T}\,\mathcal S\cdot x$, where $\mathcal S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height at least $c$ and window square `xWindowSq` at most $u^2$, and with `archDetNorm` $w\,g\in[d_1,d_2]$ for every $w$; assume `CoversModCentre F W`, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\,z\in W$, the embedding being `globalPoints` and $z$ acting through `centralScalar`. Let $\alpha,\beta\in\mathbb R$ with $0<\alpha$, and let $S$ be a subset of the determinant-norm slab $\{g\mid \|\det g\|_{\mathbb A}\in[\alpha,\beta]\}$ (idele norm as in [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)) which is a fundamental domain for the left action of the image of $\mathrm{GL}_2(F)$ under `globalPoints` with respect to the adelic Haar measure `adelicGLHaar` restricted to that slab. Let $\xi$ be a homomorphism from the centre subgroup of the pins `productionPinsOf F W (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)` — this subgroup being all of $(\mathbb{A}_F)^\times$ — to $\mathbb{C}^\times$, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$. Then, if `IsAutomorphicFnAt` holds for $\xi$ and $\varphi$ at those pins, it also holds at the pins formed in exactly the same way with $S$ in place of $W$. Since `IsAutomorphicFnAt` evaluates the predicate `LsXiMember` at the pins' measurable space `glBorel`, measure `adelicGLHaar`, central subgroup and set $D$, and the two pins differ only in $D$, the assertion is that the automorphy condition over the window $W$ implies the one over $S$, for the same $\varphi$ and the same central character.
--
--   This is the change-of-domain step in the adelic theory of automorphic forms on $\mathrm{GL}_2$: a square-integrability-with-central-character condition imposed over an explicit finite union of translated centre-cut Siegel sets is transferred to an arbitrary measurable fundamental domain inside a slab where the idele norm of the determinant is bounded above and below, using reduction theory for $\mathrm{GL}_2$ over a number field. It is invoked throughout the construction of the cuspidal spectrum and of Hecke-stable submodules of automorphic functions, where the fundamental-domain formulation is the convenient one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) (S : Set (AdelicGL2 (𝓞 F) F))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : IsAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ) :
    IsAutomorphicFnAt F
      (productionPinsOf F S
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ := by sorry
