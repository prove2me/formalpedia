-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_analyticOnNhd_integral_archTorus_pair
-- name    : AutomorphicForm.RankinSelberg.analyticOnNhd_integral_archTorus_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b6d48da8-f1e7-5d2a-875f-0128cc31251b
-- title:
--   Analyticity of an archimedean torus Rankin–Selberg pairing
-- statement:
--   Let $K$ be a number field, $D_0$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ and $w$ a real number, and let $x_0,y,f_\infty\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous. Throughout, $W_\varphi(g)$ denotes `whittakerCoefficient` of $\varphi$ at $\alpha=1$ for the production pins attached to $D_0$, to the level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, to the Hecke generators $\mathrm{heckeGen}(v)$ and to the box $\mathrm{adelicBox}(K)$, and for the standard additive character $\psi_K$: that is, $W_\varphi(g)=\int \varphi(u(x)g)\,\psi_K(-x)\,d\nu(x)$, $u(x)$ the upper unipotent matrix, $\nu$ the additive adelic Haar measure conditioned to $\mathrm{adelicBox}(K)$. Assume: $\|f_\infty(k)\|\le B_f$ for all $k$ with trivial finite part whose archimedean components $k_{v}$ satisfy `IsRowIsometry` (determinant of norm $1$, and the row action of $k_v$ preserves $\|x\|^2+\|y\|^2$); $t_0$ is an idele with archimedean part $1$ and $\kappa\in\mathrm{GL}_2(\mathbb{A}_K)$ has trivial archimedean part; $\delta_x,\delta_y>0$ and, for all such $k$ and all ideles $a$ with trivial finite part, $\|W_{x_0}(\mathrm{diag}(a,1)k\,\mathrm{diag}(t_0,1)\kappa)\|\le C_x\prod_{v\mid\infty}\|a_v\|^{m_v w/2}\min(1,\|a_v\|)^{\delta_x}$ and $\|W_{y}(\mathrm{diag}(a,1)k\,\mathrm{diag}(t_0,1))\|\le C_y\prod_{v\mid\infty}\|a_v\|^{m_v w/2}\min(1,\|a_v\|)^{\delta_y}$, with $m_v=\mathrm{mult}(v)$; and, for each $M\in\mathbb{N}$, constants bounding the same two quantities by $C_M\,\|a\|^{w/2}\|a_v\|^{-M}$ at every archimedean $v$. Then $$s\mapsto\int f_\infty(k)\Big(\int \|a\|^{s+1/2}\,\|a\|^{-w-1}\,W_{x_0}(\mathrm{diag}(a,1)k\,\mathrm{diag}(t_0,1)\kappa)\,\overline{W_{y}(\mathrm{diag}(a,1)k\,\mathrm{diag}(t_0,1))}\,d\mathrm{sPartMeasure}_\emptyset(a)\Big)d k$$ is analytic on a neighbourhood of each point of $\{s:\ \mathrm{Re}\,s>1/2-(\delta_x+\delta_y)/2\}$, where $\|a\|$ is the idele norm, the outer integral is over the subgroup of the adelic maximal compact consisting of elements trivial at every finite place with its Haar measure, and $\mathrm{sPartMeasure}_\emptyset$ is the image under $\mathrm{partAt}_\emptyset$ of idelic Haar measure restricted to the ideles that are integral, with integral inverse, at all finite places.
--
--   This is the holomorphy step for the Rankin–Selberg pairing of two Whittaker functions integrated over the archimedean torus: the two-sided decay hypotheses ($\min(1,\|a_v\|)^{\delta}$ at the small end, arbitrary polynomial decay at the large end) push analyticity of the resulting zeta-type integral from $\mathrm{Re}\,s>1/2$ to the half-plane $\mathrm{Re}\,s>1/2-(\delta_x+\delta_y)/2$, hence past the centre. It feeds [`AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery`](thm.html#AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_pair_and_ne_zero_of_ball_surgery).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_analyticOnNhd_integral_archTorus_pair.lean

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.RankinSelberg.analyticOnNhd_integral_archTorus_pair
    (K : Type) [Field K] [NumberField K]
    (D₀ : Set (AdelicGL2 (𝓞 K) K)) (w : ℝ)
    (x₀ y finf : AdelicGL2 (𝓞 K) K → ℂ) (_hx₀c : Continuous x₀) (_hyc : Continuous y) (_hfc : Continuous finf)
    (Bf : ℝ) (_hBf : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) → ‖finf k‖ ≤ Bf)
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1) (κ : AdelicGL2 (𝓞 K) K) (_hκ : glArch (𝓞 K) K κ = 1)
    (δx Cx : ℝ) (_hδx : 0 < δx)
    (_hCx : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
        (diagOne a * k * (diagOne t₀ * κ))‖ ≤
          Cx * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δx))
    (δy Cy : ℝ) (_hδy : 0 < δy)
    (_hCy : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
        (diagOne a * k * (diagOne t₀))‖ ≤
          Cy * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δy))
    (_hxlarge : ∀ M : ℕ, ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * (diagOne t₀ * κ))‖ ≤
          Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))
    (_hylarge : ∀ M : ℕ, ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
        ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * k * (diagOne t₀))‖ ≤
          Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
            (∫ a, ((NumberField.TateGlobal.ideleNorm K a : ℝ) : ℂ) ^ (s + 1 / 2) *
              ((NumberField.TateGlobal.ideleNorm K a ^ (-w - 1) : ℝ) : ℂ) *
              (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * (diagOne t₀ * κ)) *
                (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne a * (k : AdelicGL2 (𝓞 K) K) * diagOne t₀)))
            ∂(NumberField.Idele.sPartMeasure K ∅))
          ∂(maximalCompactAtHaar K ∅))
      {s : ℂ | 1 / 2 - (δx + δy) / 2 < s.re} := by sorry
