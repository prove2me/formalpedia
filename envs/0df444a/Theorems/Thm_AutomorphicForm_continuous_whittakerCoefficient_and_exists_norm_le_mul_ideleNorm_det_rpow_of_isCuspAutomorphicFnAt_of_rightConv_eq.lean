-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq
-- name    : AutomorphicForm.continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/a3134f95-fc36-5e1e-a3dd-2362a14cdd96
-- title:
--   Continuity and norm bound for GL₂ Whittaker coefficients
-- statement:
--   Let $K$ be a number field whose adelic group $\mathrm{GL}_2(\mathbb{A}_K)$ is assumed second countable, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $\mathfrak{D}$ for the union over $x\in T$ of the right translates by $x$ of the centre-cut Siegel set with parameters $(c,u,d_1,d_2)$, i.e. of the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place $w$ has local height at least $c$ and squared $x$-window at most $u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$. Assume $\mathfrak{D}$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z\in\mathfrak{D}$. Let `pins` be the production carrier data attached to $\mathfrak{D}$, the level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$, the Hecke generators $v\mapsto \mathrm{heckeGen}(v)$ and the adelic box $\{x: x_\infty\in \mathrm{infiniteBox}, x_{\mathrm{fin}}\text{ integral}\}$; its central subgroup is all of $\mathbb{A}_K^\times$ and its additive measure $\nu$ is the adelic additive Haar measure conditioned on that box. Let $\chi$ be a homomorphism from that central subgroup to $\mathbb{C}^\times$, and let $\varphi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, satisfy `IsCuspAutomorphicFnAt` for `pins` and $\chi$ (membership in the $L^2$-with-central-character space attached to $\mathfrak{D}$ and the adelic Haar measure, together with vanishing of the constant term along `unipotentGL2` against $\nu$), and be fixed by right convolution against some factorizable test function $f$, that is $g\mapsto\int\varphi(gx)f(x)\,d\mu(x)$ equals $\varphi$. Let $\psi$ be an additive character of $\mathbb{A}_K$ that is continuous and satisfies $\|\psi(x)\|=1$ for all $x$, and let $\alpha\in K$. Then the Whittaker coefficient $g\mapsto\int\varphi(\mathrm{unipotentGL2}(x)\,g)\,\psi(-\alpha x)\,d\nu(x)$ is continuous, and there exist real numbers $M$ and $r$ such that its norm at every $g$ is at most $M\cdot\|\det g\|^{r}$, where $\|\cdot\|$ is the idelic norm given by the distributive Haar character of $\mathbb{A}_K$.
--
--   This is the trivial ("convexity") growth bound for the global Whittaker functions of a smoothed adelic cusp form on $\mathrm{GL}_2$, together with their continuity. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, where integrability of the cell integrands built from Whittaker functions and their duals is established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.continuous_whittakerCoefficient_and_exists_norm_le_mul_ideleNorm_det_rpow_of_isCuspAutomorphicFnAt_of_rightConv_eq
    (K : Type) [Field K] [NumberField K] [SecondCountableTopology (AdelicGL2 (𝓞 K) K)]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (hsmooth : ∃ f : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K f ∧ rightConv K φ f = φ)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψc : Continuous ψ) (hψ1 : ∀ x, ‖ψ x‖ = 1) (α : K) :
    Continuous (whittakerCoefficient K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ψ φ α) ∧
    ∃ M r : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ψ φ α g‖ ≤
        M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ r := by sorry
