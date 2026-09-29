-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_unipotentAverage_rightConv
-- name    : AutomorphicForm.continuous_unipotentAverage_rightConv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/1c042998-6651-5ff5-a993-42030185f4fa
-- title:
--   Continuity of the unipotent average of φ * f
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\{g x : g \in \Sigma\}$, where $\Sigma$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$, i.e. the set of $g$ whose finite component lies in the integral subset `finiteIntegralGL2`, whose archimedean component has local height at least $c$ and $x$-window square at most $u^2$ at every infinite place, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ can be written with $\gamma\in\mathrm{GL}_2(F)$ and a central adelic scalar $z$ so that $\gamma g z\in D$. Let `pins` be the carrier data `productionPinsOf` attached to $D$, with Borel subgroup and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, full central subgroup $Z=\top$, level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$, Hecke generators $v\mapsto$ `heckeGen`, and the conditioning of the adelic additive Haar measure to the adelic box (infinite box times integral finite adeles). Let $\xi\colon Z\to\mathbb{C}^\times$ be a character, and let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and cuspidal-automorphic at these pins with character $\xi$ (automorphic at the pins, and cuspidal for the unipotent $x\mapsto n(x)$ against the conditioned measure). Let $f$ be a factorizable test function, that is $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ an archimedean and $f_{\mathrm{fin}}$ a finite test factor, and let $B$ lie in the Schwartz–Bruhat space of $\mathbb{A}_F$, the $\mathbb{C}$-span of pure tensors. Finally let $\Phi$ satisfy $\Phi(h)=\int_{\mathbb{A}_F} B(x)\,(\varphi * f)(h\,n(x))\,dx$ for all $h$, the integral being against adelic additive Haar measure, where $(\varphi*f)(g)=\int \varphi(gx)f(x)\,dx$ over $\mathrm{GL}_2(\mathbb{A}_F)$ with its Haar measure. Then $\Phi$ is continuous.
--
--   The statement provides the regularity input needed to treat $a\mapsto\Phi(\mathrm{diag}(a,1))$ as an honest integrand in the torus zeta integrals of the Jacquet–Langlands theory of automorphic forms on $\mathrm{GL}_2$. It is used in the construction of the zeta integral of the Whittaker coefficient of $\Phi$, in particular by the results on integrability and holomorphy of those integrals and by the Whittaker expansion at the identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_unipotentAverage_rightConv.lean

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

theorem AutomorphicForm.continuous_unipotentAverage_rightConv
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
        ∫ x, B x * rightConv F φ f (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) :
    Continuous Φ := by sorry
