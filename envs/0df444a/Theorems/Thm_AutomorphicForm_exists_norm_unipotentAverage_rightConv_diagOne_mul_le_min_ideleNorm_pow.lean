-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow
-- name    : AutomorphicForm.exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/fece7afc-fb86-57e4-897a-b76aaf71b6ec
-- title:
--   Two-sided torus decay of a smoothed cuspidal unipotent average
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\,(\cdot\,x)\,[\,\Sigma\,]$, where $\Sigma$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$: those $g$ whose finite part lies in the integral subgroup $\mathrm{GL}_2(\hat{\mathcal O}_F)$, whose archimedean component at each infinite place $w$ has local height $\ge c$, window coordinate $x$-square $\le u^2$ and determinant norm in $[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\,z\in D$. Let $\xi$ be a homomorphism from the group of ideles (the subgroup $\top$ carried by the production pins attached to $D$, the levels $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators at finite places, and the box $\mathrm{adelicBox}\,F$) to $\mathbb{C}^\times$, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and cuspidal automorphic for these pins and $\xi$: it satisfies the predicate `LsXiMemberAt` for the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the set $D$, the full idele group and $\xi$, and its constant term along $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$, formed with the adelic additive Haar measure conditioned on $\mathrm{adelicBox}\,F$, vanishes at every point. Let $f$ be a factorizable test function, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ smooth in the matrix entries and compactly supported and $f_{\mathrm{fin}}$ locally constant and compactly supported, and let $B$ lie in the Schwartz–Bruhat space of $\mathbb{A}_F$ (the $\mathbb{C}$-span of pure tensors of a Schwartz function on the mixed space with a locally constant compactly supported function on the finite adeles). Let $\Phi$ satisfy $\Phi(h)=\int_{\mathbb{A}_F} B(x)\,(\varphi*f)\bigl(h\,n(x)\bigr)\,dx$ for all $h$, where $\varphi*f(g)=\int \varphi(gy)f(y)\,dy$ against Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ and $dx$ is adelic additive Haar measure. Then for every compact $C\subseteq \mathrm{GL}_2(\mathbb{A}_F)$ and every $k\in\mathbb{N}$ there is a real constant $\mathrm{Cst}$ with $\|\Phi(\mathrm{diag}(a,1)\,g)\|\le \mathrm{Cst}\cdot\min(\|a\|,\|a\|^{-1})^{k}$ for every idele $a$ and every $g\in C$, where $\|a\|$ is the idelic norm given by the distributive Haar character of $a$ on $\mathbb{A}_F$.
--
--   This is the two-sided rapid decay along the diagonal torus of the Schwartz–Bruhat unipotent average of a smoothed cusp form: decay faster than any power of $\min(\|a\|,\|a\|^{-1})$, uniformly for $g$ in a compact set. It is the convergence input for the global zeta integrals of such averages, and is used in [`AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq`](thm.html#AutomorphicForm.exists_differentiable_forall_integral_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal

theorem AutomorphicForm.exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow
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
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * rightConv F φ f (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (k : ℕ) :
    ∃ Cst : ℝ, ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), g ∈ C →
      ‖Φ (diagOne a * g)‖ ≤ Cst * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k := by sorry
