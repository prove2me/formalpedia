-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
-- name    : AutomorphicForm.exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/a68f05ad-df91-58a2-b89b-c0722c6cc8fc
-- title:
--   Moderate growth in det of a smoothed adelic cusp form
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $\mathfrak{S}$ for the union over $x\in T$ of the right translates $\{gx : g\in \mathcal{S}\}$ of the centre-cut Siegel set $\mathcal{S}$ consisting of those $g$ whose finite part lies in the integral finite-adelic subset `finiteIntegralGL2` and whose archimedean component at each infinite place $w$ has local height at least $c$, squared $x$-window at most $u^2$, and archimedean determinant norm $\mathrm{archDetNorm}\,w\,g$ in $[d_1,d_2]$. Assume $\mathfrak{S}$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\,\mathrm{diag}(z,z)\in\mathfrak{S}$. Fix the pins `productionPinsOf` attached to $\mathfrak{S}$, with the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, central subgroup the whole idele unit group, level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators `heckeGen`, and the additive adelic Haar measure conditioned on `adelicBox`; let $\xi$ be a homomorphism from that central subgroup to $\mathbb{C}^\times$ and let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous, satisfy the $L^s$-membership condition `LsXiMemberAt` with central character $\xi$ at these pins, and be cuspidal against the unipotent subgroup for the conditioned measure. Let $f$ be factorizable, i.e. $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for an archimedean test factor $f_\infty$ and a finite test factor $f_{\mathrm{fin}}$. Then there exist a real $C$ and a natural number $M$ such that for all $g$ the right convolution $(\varphi*f)(g)=\int \varphi(gx)f(x)\,dx$ satisfies $\|(\varphi*f)(g)\|\le C\,\max\bigl(\|\det g\|,\|\det g\|^{-1}\bigr)^{M}$, where $\|\cdot\|$ is the idele norm given by the Haar modulus.
--
--   This is the moderate-growth estimate for a smoothed cuspidal function on $\mathrm{GL}_2(\mathbb{A}_F)$, in the form of a polynomial bound in the idelic determinant norm, with no unitarity assumed on the central character. It is used downstream in the continuity of unipotent averages of right convolutions and in the construction of the Whittaker expansion and Euler product attached to an arithmetically realizable cusp form; it is obtained from the corresponding bound on determinant slabs together with the fact that a continuous idele class character has absolute value a power of the idele norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal

theorem AutomorphicForm.exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
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
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖rightConv F φ f g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M := by sorry
