-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self
-- name    : AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/3c0d8b3c-73e1-51e3-b65a-bc1bf2938592
-- title:
--   Rankin–Selberg package for one continuous GL₂ cusp realisation
-- statement:
--   Let $K$ be a number field and let $\alpha$ be the character of the idele group $(\mathbf{A}_K)^\times \to \mathbb{R}^\times$ obtained from the module (distributive Haar) character of $\mathbf{A}_K$, assumed pointwise positive via $h\alpha$. Fix reals $c,u,d_1,d_2$ with $c>0$, $0<d_1<d_2$, a finite set $T \subset \mathrm{GL}_2(\mathbf{A}_K)$ such that $D := \bigcup_{x\in T} (\cdot\, x)\,[\,\text{centreCutSiegelSet}\ K\,c\,u\,d_1\,d_2\,]$ satisfies `CoversModCentre`, i.e. every $g$ has $\gamma g z \in D$ for some $\gamma \in \mathrm{GL}_2(K)$ and some central idele $z$. Let $\Theta$ be a Hecke eigensystem over $K$ with coefficients in $\mathbb{C}$ (a nonzero level ideal and families $a_v, b_v$), let $R$ be a smooth cusp realisation at the production pins built from $D$, from the levels $U(N)=\mathrm{levelOne}(N)\cap \mathrm{GL}_2(\mathbf{A}_K)_{\mathrm{fin}}$, from the Hecke generators $\mathrm{heckeGen}(v)$ and from the box `adelicBox K`, for the twisted system $\Theta^{\mathrm{raw}}$ (same level and $a_v$, with $b_v$ replaced by $N(v)^{-1}b_v$), with $R$ genuine, meaning $R.\mathrm{toFun}$ continuous. Let `tys` be a family of archimedean types, and $V$ a $\mathbb{C}$-submodule of functions on $\mathrm{GL}_2(\mathbf{A}_K)$ that is a cuspidal constituent for the central character of $R$ (an irreducible cusp subrepresentation), with $R.\mathrm{toFun}$ lying in the intersection of $V$, the submodule invariant under $U(\Theta.\mathrm{level})$ on the right, and the archimedean type cut of `tys`. Then there exist a finite set $S$ of finite places, a function $f$, a family $\varphi : \mathbb{C} \to (\mathrm{GL}_2(\mathbf{A}_K) \to \mathbb{C})$, reals $w, e_1, e_2, a, \sigma_0$, a constant $C \in \mathbb{C}$, a set $\mathcal{F}$ and functions $A, L, \zeta_i : \mathbb{C} \to \mathbb{C}$ with the following properties. Every $v \notin S$ satisfies $v \nmid \Theta.\mathrm{level}$ and $v \notin R.\mathrm{exceptionalSet}$; $f$ is a factorisable test function (a smooth compactly supported archimedean factor in the matrix entries times a locally constant compactly supported finite factor); for each $s$ the function $\varphi_s$ is an induced section for the pair of characters $\alpha^{s+1/2}, \alpha^{-(s+1/2)}$ on the diagonal of the adelic Borel subgroup, is archimedean $K$-finite and $K_f$-smooth, the map $(s,g) \mapsto \varphi_s(g)$ is continuous, and $s \mapsto \varphi_s(g)$ is entire for each $g$; $0 < e_1 < e_2$ and $\mathcal{F}$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(K)$ on $\mathrm{GL}_2(\mathbf{A}_K)$ with respect to adelic Haar measure restricted to the slab $\{g : \|\det g\| \in [e_1,e_2]\}$; $a < 1/2 < \sigma_0$ and $C \neq 0$. Writing $x := \mathrm{rightConv}(R.\mathrm{toFun}, f)$ for the right convolution $g \mapsto \int R(gy) f(y)\,dy$, and $I(s)$ for the Petersson integral of weight $w$ over $\mathcal{F}$ of $x \cdot \bigl(\varphi_s + \sum_{\xi \in K} \varphi_s(w_2\,u(\xi)\,\cdot)\bigr)$ against $x$, where $w_2$ is the adelic Weyl element and $u(\xi)$ the upper unipotent matrix: $A$ is analytic on a neighbourhood of $\{\operatorname{Re} s > a\}$, $A(s) = (s - 1/2)\,I(s)$ for $\operatorname{Re} s > 1/2$, and $A(1/2) \neq 0$. Further, $s \mapsto J(s) := \mathrm{sPartIntegral}\,K\,S$ (at the same pins, with the standard additive character, both arguments $x$, section $\varphi_s$, and parameters $w, e_1, e_2$) is analytic on a neighbourhood of $\{\operatorname{Re} s > a\}$ and $J(\sigma)$ is real and strictly positive for real $\sigma > a$. The function $\zeta_i$ is analytic on a neighbourhood of $\{\operatorname{Re} s > a\}$, is nonzero there, is given by the convergent product $\prod_{v \notin S}\bigl(1 - N(v)^{-(2s+1)}\bigr)$, and is real and strictly positive at real $\sigma > a$. Finally $L$ is analytic on a neighbourhood of $\{\operatorname{Re} s > \sigma_0\}$ and for $\operatorname{Re} s > \sigma_0$ the product over $v \notin S$ of the inverses of $\mathrm{rsEulerPoly}(a_v/b_v,\, b_v^{-1},\, a_v,\, b_v,\, 0)$ evaluated at $N(v)^{-(s+1/2)}$ converges to $L(s)$, and $I(s) = C \cdot J(s) \cdot \zeta_i(s) \cdot L(s)$.
--
--   This is the Rankin–Selberg integral representation for the pair $(\Theta, \tilde{\Theta})$ attached to a single continuous cusp realisation: the regularised Petersson integral against the Bruhat form of the Eisenstein section factors as a constant times the $S$-part integral, an inverse partial zeta factor and the partial Euler product of degree-six Rankin–Selberg polynomials, with the pole of the Eisenstein family at $s = 1/2$ surviving ($A(1/2) \neq 0$). It is the analytic input to the downstream statements producing meromorphic continuation of that Euler product with a first-order pole and positive residue, used in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
      (_hc : 0 < c) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (_hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
      (Θ : HeckeEigensystem K ℂ)
      (R : SmoothCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
      (_hR : IsGenuineCuspRealizationAt K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
      (tys : AutomorphicForm.ArchTypeFamily K)
      (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
      (_hV : IsCuspConstituent K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar V)
      (_hRV : R.toFun ∈ V ⊓ levelInvariantSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.level ⊓ archCutSubmodule K tys),
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : AdelicGL2 (𝓞 K) K → ℂ) (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (w e₁ e₂ a σ₀ : ℝ) (C : ℂ) (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (A L ζi : ℂ → ℂ),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet) ∧
      IsFactorizableTestFn K f ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s)) ∧
      (∀ s, IsArchKFinite K (φ s)) ∧ (∀ s, IsKfSmooth K (φ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => φ s g)) ∧
      0 < e₁ ∧ e₁ < e₂ ∧
      IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) ∧
      a < 1 / 2 ∧ 1 / 2 < σ₀ ∧ C ≠ 0 ∧
      AnalyticOnNhd ℂ A {s : ℂ | a < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        A s = (s - 1 / 2) * peterssonIntegral K w 𝓕
          (fun g => rightConv K R.toFun f g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) (rightConv K R.toFun f)) ∧
      A (1 / 2) ≠ 0 ∧

      AnalyticOnNhd ℂ (fun s : ℂ => RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ s) w e₁ e₂)
        {s : ℂ | a < s.re} ∧
      (∀ σ : ℝ, a < σ →
        (RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ σ) w e₁ e₂).im = 0 ∧
        0 < (RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ σ) w e₁ e₂).re) ∧

      AnalyticOnNhd ℂ ζi {s : ℂ | a < s.re} ∧
      (∀ s : ℂ, a < s.re → ζi s ≠ 0 ∧
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) (ζi s)) ∧
      (∀ σ : ℝ, a < σ → (ζi σ).im = 0 ∧ 0 < (ζi σ).re) ∧

      AnalyticOnNhd ℂ L {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + 1 / 2))))⁻¹) (L s) ∧
        peterssonIntegral K w 𝓕
          (fun g => rightConv K R.toFun f g * (φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K *
            unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g))) (rightConv K R.toFun f) =
        C * RankinSelberg.sPartIntegral K S
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ s) w e₁ e₂ *
          ζi s * L s) := by sorry
