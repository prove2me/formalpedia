-- Prove2me | Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_toFun_eq_rightConv_of_isArithGenuineCuspRealizable
-- name    : AutomorphicForm.exists_smoothCuspRealizationAt_toFun_eq_rightConv_of_isArithGenuineCuspRealizable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/cc69e5ef-2f34-5ef8-a200-bd63495c3179
-- title:
--   Smoothing a cusp realization by convolution with a test function
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Write $D=\bigcup_{x\in T}\,\{g x : g\in \mathcal{S}\}$ for the union of the right translates by $T$ of the centre-cut Siegel set $\mathcal{S}$ cut out by the conditions that the finite part of $g$ be finite-integral, that $c\le$ the local height and the $x$-window square be $\le u^2$ at every infinite place, and that every archimedean determinant norm lie in $[d_1,d_2]$; assume $D$ covers modulo the centre, i.e. for every $g$ there are $\gamma\in \mathrm{GL}_2(F)$ and a unit $z$ of $\mathbb{A}_F$ with $\gamma g\,\mathrm{diag}(z,z)\in D$. Let $\Phi$ be a Hecke eigensystem over $F$ with values in $\mathbb{C}$ (a nonzero level ideal together with families $a,b$ indexed by the height-one primes of $\mathcal{O}_F$), and let $\mathrm{pins}$ be the production pins built from the window $D$, the level groups $N\mapsto \mathrm{levelOne}(N)\cap \ker(\mathrm{glArch})$, the Hecke generators $v\mapsto \mathrm{heckeGen}(v)$ and the adelic box, with full central subgroup $Z=\top$, adelic $\mathrm{GL}_2$ Haar measure and the additive Haar measure conditioned on the box. Assume $\Phi$ is arithmetically genuinely cusp-realizable at $\mathrm{pins}$, that is, the rescaled eigensystem $\Phi.\mathrm{toRawCentral}$ (same level and same $a$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$) satisfies $\mathrm{IsGenuineCuspRealizable}$. Then there exist a smooth-cusp realization $R$ of $\Phi.\mathrm{toRawCentral}$ at $\mathrm{pins}$ (a nowhere-zero-somewhere function on $\mathrm{GL}_2(\mathbb{A}_F)$ with a central character, smooth cuspidal automorphic at $\mathrm{pins}$, invariant under the level group at $\Phi.\mathrm{level}$, and, outside a finite exceptional set of primes, an eigenfunction for the Hecke coset operators with eigenvalues $a_v$ and for the central scalars $\det(\mathrm{gen}\,v)$ with eigenvalues $(\mathrm{cNorm}\,v)^{-1}b_v$), a character $\xi\colon Z\to\mathbb{C}^\times$ and functions $\varphi,f\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that $\varphi$ is a cuspidal automorphic function at $\mathrm{pins}$ with central character $\xi$, $\varphi$ is continuous, $f$ is a factorizable test function (a product of an archimedean test factor evaluated at the archimedean part and a finite test factor evaluated at the finite part), $R.\mathrm{toFun}$ equals the right convolution $g\mapsto \int \varphi(gx)f(x)\,dx$ against the adelic $\mathrm{GL}_2$ Haar measure, and $R.\mathrm{toFun}$ is continuous.
--
--   This is the smoothing step for adelic $\mathrm{GL}_2$ automorphic forms: any genuine cusp realization of a Hecke eigensystem on the given Siegel window can be replaced by the convolution of a continuous cuspidal automorphic function with a factorizable test function, without losing the level, Hecke and central eigen-properties. It is used in the construction of the Euler product and analytic continuation of the twisted $L$-series attached to such an eigensystem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_smoothCuspRealizationAt_toFun_eq_rightConv_of_isArithGenuineCuspRealizable.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.exists_smoothCuspRealizationAt_toFun_eq_rightConv_of_isArithGenuineCuspRealizable
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (hΦ : IsArithGenuineCuspRealizable F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Φ) :
    ∃ (R : SmoothCuspRealizationAt F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Φ.toRawCentral)
      (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
      (φ f : AdelicGL2 (𝓞 F) F → ℂ),
      IsCuspAutomorphicFnAt F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ ∧
      Continuous φ ∧ IsFactorizableTestFn F f ∧ R.toFun = rightConv F φ f ∧ Continuous R.toFun := by sorry
