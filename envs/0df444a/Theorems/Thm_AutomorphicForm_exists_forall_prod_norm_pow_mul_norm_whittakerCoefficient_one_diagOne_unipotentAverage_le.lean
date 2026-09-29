-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_prod_norm_pow_mul_norm_whittakerCoefficient_one_diagOne_unipotentAverage_le
-- name    : AutomorphicForm.exists_forall_prod_norm_pow_mul_norm_whittakerCoefficient_one_diagOne_unipotentAverage_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/f3861d29-027f-5fc4-b775-83dbfbfe60b6
-- title:
--   Uniform decay of the first Whittaker coefficient along the torus
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}(\cdot\,x)''\,$ of the centre-cut Siegel set with parameters $c,u,d_1,d_2$ (those $g$ whose finite part lies in $\mathrm{GL}_2$ of the integral finite adèles, whose local height at each infinite place is at least $c$, whose window quantity `xWindowSq` at each infinite place is at most $u^2$, and whose archimedean determinant norms all lie in $[d_1,d_2]$), and assume `CoversModCentre F D`: every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idèle unit $z$ with $\gamma g z\in D$. Let `pins` be the production pins built from $D$, the levels $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $v\mapsto \mathrm{heckeGen}(v)$ and the adelic box, so that the group is $\top$, the measures are Borel Haar on $\mathrm{GL}_2(\mathbb{A}_F)$ and additive Haar conditioned on the box on $\mathbb{A}_F$; let $\xi$ be a character of that group, and let $\varphi$ be continuous with `IsCuspAutomorphicFnAt F pins ξ φ`, i.e. $\varphi$ satisfies `LsXiMemberAt` for these pins and $\xi$ and all its constant terms along $x\mapsto n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ vanish. Let $f$ be a factorizable test function, $f(g)=f_\infty(\mathrm{glArch}\,g)f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ compactly supported and smooth in the archimedean matrix entries and $f_{\mathrm{fin}}$ locally constant of compact support; let $B$ lie in the Schwartz–Bruhat space of $\mathbb{A}_F$; let $\Phi(h)=\int B(x)\,(\varphi * f)(h\,n(x))\,dx$ against adelic additive Haar, where $(\varphi*f)(g)=\int \varphi(gy)f(y)\,dy$ against Haar on $\mathrm{GL}_2(\mathbb{A}_F)$; and let $\psi$ be an additive character of $\mathbb{A}_F$ that is trivial on $F$, continuous and nontrivial. Then there is $M\in\mathbb{N}$ such that for every family $m\colon\{w\mid\infty\}\to\mathbb{N}$ there is a real $C$ with $$\Big(\prod_{w}\|(b_\infty)_w\|^{m(w)}\Big)\,\big\|W_1(\Phi)(\mathrm{diag}(b,1))\big\|\le C\,\max\big(\|b\|,\|b\|^{-1}\big)^M$$ for all idèle units $b$, where $W_1(\Phi)(g)=\int \Phi(n(x)g)\,\psi(-x)\,d\nu(x)$ with $\nu$ the box-conditioned additive Haar measure of the pins, and $\|b\|$ is the idèle norm given by the module of $b$. The exponent $M$ does not depend on $m$.
--
--   This is the archimedean rapid-decay estimate for the first Whittaker coefficient of a unipotent Schwartz–Bruhat average of a smoothed cusp form, restricted to the torus $\mathrm{diag}(b,1)$, with an exponent of polynomial loss in the idèle norm that is uniform in the prescribed archimedean decay orders. It feeds the integrability statement for the zeta integrand attached to such Whittaker coefficients, [`AutomorphicForm.exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage`](thm.html#AutomorphicForm.exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_prod_norm_pow_mul_norm_whittakerCoefficient_one_diagOne_unipotentAverage_le.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

theorem AutomorphicForm.exists_forall_prod_norm_pow_mul_norm_whittakerCoefficient_one_diagOne_unipotentAverage_le
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
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) :
    ∃ M : ℕ, ∀ m : InfinitePlace F → ℕ, ∃ C : ℝ, ∀ b : (AdeleRing (𝓞 F) F)ˣ,
      (∏ w : InfinitePlace F, ‖((b : AdeleRing (𝓞 F) F).1 w)‖ ^ m w) *
        ‖whittakerCoefficient F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 (diagOne b)‖
          ≤ C * max (ideleNorm F b) (ideleNorm F b)⁻¹ ^ M := by sorry
