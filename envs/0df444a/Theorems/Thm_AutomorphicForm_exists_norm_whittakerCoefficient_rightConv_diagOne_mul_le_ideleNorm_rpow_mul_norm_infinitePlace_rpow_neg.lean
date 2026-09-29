-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg
-- name    : AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/57e2e0f7-dd1b-5b8f-b018-1128bdee50bd
-- title:
--   Coordinatewise rapid decay of smoothed cuspidal Whittaker coefficients
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$. Write $D=\bigcup_{x\in T}\{g x : g\in \mathrm{centreCutSiegelSet}\}$, where the centre-cut Siegel set consists of those $g$ whose finite part lies in the integral subgroup `finiteIntegralGL2`, whose archimedean component at each infinite place has local height at least $c$, window quantity `xWindowSq` at most $u^2$, and determinant norm in $[d_1,d_2]$; assume $D$ covers the group modulo centre, i.e. every $g$ admits $\gamma\in \mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g z\in D$. Let `pins` be `productionPinsOf` for $D$, the levels $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke elements $\mathrm{heckeGen}(v)$, and the box `adelicBox`; its central group is all of the idele units, its measures are the adelic $\mathrm{GL}_2$-Haar measure and the additive adelic Haar measure conditioned on `adelicBox`. Let $\chi$ be a character of that central group with values in $\mathbb{C}^\times$, and let $\varphi$ be continuous, automorphic for these data with central character $\chi$, and cuspidal in the sense that its constant term along the unipotent $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ vanishes identically. Let $f$ be a factorizable test function, that is $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ given by a smooth function of the matrix entries in the mixed space and compactly supported, and $f_{\mathrm{fin}}$ locally constant and compactly supported; let $x=\mathrm{rightConv}\,\varphi\,f$, the integral $g\mapsto\int \varphi(gy)f(y)$. Let `tys` be a family assigning to each infinite place $w$ finitely many archimedean representation types, and assume $x$ lies in the corresponding cut submodule $\bigsqcap_w \bigvee_i$ of type submodules. Let $w_0\in\mathbb{R}$ satisfy $\|\chi(z)\|=\|z\|_{\mathbb{A}}^{w_0}$ for every idele $z$, where $\|\cdot\|_{\mathbb{A}}$ is the module `ideleNorm`, and let $m\in\mathbb{N}$. Then there is a constant $C$ such that for every $k$ with trivial finite part and with each archimedean component satisfying `IsRowIsometry` (determinant of norm $1$ and preservation of the sum of squared norms of the two coordinates), every idele $a$ with finite part $1$, and every infinite place $w$, the Whittaker coefficient of $x$ at $\alpha=1$ for the standard additive character, evaluated at $\mathrm{diag}(a,1)\,k$, has $$\big\|W_1(x)(\mathrm{diag}(a,1)k)\big\|\le C\,\|a\|_{\mathbb{A}}^{w_0/2}\,\|a_w\|^{-m}.$$
--
--   This is the rapid decay of the archimedean Whittaker function of a $K_\infty$-finite smoothed cusp form, recorded in per-place currency: decay faster than any fixed power in each single archimedean coordinate, with a constant uniform in the maximal-compact variable $k$ and in the place $w$, and with the bookkeeping factor $\|a\|_{\mathbb{A}}^{w_0/2}$ coming from the central modulus. It feeds the convergence and analyticity statements for Rankin–Selberg integrals attached to such forms, and the construction of isotypic smoothed cusp forms with Whittaker bounds.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (tys : AutomorphicForm.ArchTypeFamily K) (hxt : rightConv K φ f ∈ archCutSubmodule K tys)
    (w₀ : ℝ) (hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ideleNorm K z ^ w₀)
    (m : ℕ) :
    ∃ C : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ w : InfinitePlace K,
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K φ f) 1
            (diagOne a * k)‖ ≤ C * ideleNorm K a ^ (w₀ / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ (-(m : ℝ)) := by sorry
