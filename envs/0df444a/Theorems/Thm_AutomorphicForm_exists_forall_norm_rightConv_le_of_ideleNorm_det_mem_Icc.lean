-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
-- name    : AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/3f75527b-c2b8-5b10-a300-2b874caedc6f
-- title:
--   Smoothed cusp forms are bounded on determinant slabs
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$. Write $D=\bigcup_{x\in T}\{s\cdot x : s\in \mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $w$, $c\le$ `localHeight`, `xWindowSq` $\le u^2$ and `archDetNorm` $w\,g\in[d_1,d_2]$. Assume `CoversModCentre F D`: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\cdot z\in D$. The carrier data are `productionPinsOf F D` with level subgroups $N\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, Hecke elements `heckeGen`, the adelic box `adelicBox F`, the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb A_F)$, and central subgroup $Z=\top$, so $\xi$ is any homomorphism from the full idele unit group to $\mathbb C^\times$. Let $\varphi:\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ be continuous and satisfy `IsCuspAutomorphicFnAt` for these pins and $\xi$, and let $f$ satisfy `IsFactorizableTestFn`, i.e. $f(g)$ is a product of an archimedean test factor in the archimedean component and a finite test factor in the finite component. Then for all reals $\alpha>0$ and $\beta$ there is $M$ with $\|(\varphi*f)(g)\|\le M$, where $(\varphi*f)(g)=\int \varphi(gx)f(x)\,dx$ against adelic Haar measure, for every $g$ whose idelic determinant norm lies in $[\alpha,\beta]$.
--
--   This is the standard statement that a cusp form on $\mathrm{GL}_2(\mathbb A_F)$, smoothed by a factorizable test function, is bounded on each slab $\alpha\le\|\det g\|_{\mathbb A}\le\beta$ of idelic determinant norm; unlike boundedness on a Siegel window, the bound here is uniform over a full slab. It feeds the bounds on archimedean derivatives of cuspidal constituents and the comparison of the norm of a cuspidal constituent with a power of the idelic determinant norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

theorem AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (α β : ℝ) (hα : 0 < α) :
    ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖rightConv F φ f g‖ ≤ M := by sorry
