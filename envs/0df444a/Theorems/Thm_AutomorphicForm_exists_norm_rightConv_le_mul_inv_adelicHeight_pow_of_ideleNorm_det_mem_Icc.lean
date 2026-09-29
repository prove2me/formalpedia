-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc
-- name    : AutomorphicForm.exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/85b27add-5134-595e-9008-9c1b172d9158
-- title:
--   Rapid decay of φ * f in the adelic height on a determinant slab
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\{s\,x : s\in \mathrm{centreCutSiegelSet}\ F\ c\ u\ d_1\ d_2\}$, where the latter set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norm at every $w$ lies in $[d_1,d_2]$. Assume `CoversModCentre` for $D$: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ can be written with $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ so that $\gamma\, g\, z$ (the scalar $z$ acting centrally) lies in $D$. Let `pins` be `productionPinsOf` for this $D$, with level subgroups $N\mapsto \mathrm{levelOne}\ N\sqcap \ker(\mathrm{glArch})$, Hecke generators $v\mapsto \mathrm{heckeGen}\ v$, and box $\mathrm{adelicBox}\ F$; its measure-theoretic data are the Borel structure `glBorel`, the Haar measure `adelicGLHaar`, central group $\top$, and on the adele ring the Borel structure `adeleBorel` with the additive Haar measure conditioned on the box. Let $\xi$ be a character of that central group with values in $\mathbb{C}^\times$, let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and satisfy `IsCuspAutomorphicFnAt` for `pins` and $\xi$, i.e. $\varphi$ belongs to the $\xi$-space `LsXiMemberAt` for these data and is cuspidal along `unipotentGL2` for the conditioned measure. Let $f$ be factorizable, $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ an archimedean and $f_{\mathrm{fin}}$ a finite test factor, and let $\alpha>0$, $\beta\in\mathbb{R}$, $k\in\mathbb{N}$. Then there exist reals $H_0$ and $C$ such that for every $h$ with $\|\det h\|_{\mathbb{A}}\in[\alpha,\beta]$ (the idele norm being the module of the distributive Haar character) and $\mathrm{adelicHeight}\ F\ h\ge H_0$, the right convolution $(\varphi * f)(h)=\int \varphi(hx)f(x)\,d\mu(x)$ satisfies $\|(\varphi*f)(h)\|\le C\,(\mathrm{adelicHeight}\ F\ h)^{-k}$, where the adelic height is the product of the archimedean height of the archimedean part and the finite height of the finite part.
--
--   This is the rapid-decay estimate for a smoothed cusp form in the adelic height, stated for an arbitrary point of a determinant slab rather than for points of a single Siegel translate; reduction theory (the central-slab covering) converts the Siegel-set form of the bound into this one. It feeds the bounds on cuspidal vectors used later, being cited by [`AutomorphicForm.exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm`](thm.html#AutomorphicForm.exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm) and by [`AutomorphicForm.forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule`](thm.html#AutomorphicForm.forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc.lean

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

theorem AutomorphicForm.exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc
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
    (α β : ℝ) (hα : 0 < α) (k : ℕ) :
    ∃ H₀ Cst : ℝ, ∀ h : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det h) ∈ Set.Icc α β → H₀ ≤ adelicHeight F h →
        ‖rightConv F φ f h‖ ≤ Cst * (adelicHeight F h)⁻¹ ^ k := by sorry
