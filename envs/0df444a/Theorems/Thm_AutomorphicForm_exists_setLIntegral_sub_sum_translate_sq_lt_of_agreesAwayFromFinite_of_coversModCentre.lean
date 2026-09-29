-- Prove2me | Theorems.Thm_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre
-- name    : AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/c8daca1c-4d1f-5339-bcbd-fb3c58be9b0f
-- title:
--   Strong multiplicity one: mean-square approximation by right translates
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$; write $D=\bigcup_{x\in T}\{gx : g\in\mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet K c u d₁ d₂` consists of those $g$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $w$, $c\le$ `localHeight`, `xWindowSq` $\le u^2$ and `archDetNorm` $\in[d_1,d_2]$. Assume `CoversModCentre`: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and a unit $z$ of $\mathbb{A}_K$ with $\gamma g\cdot\mathrm{diag}(z,z)\in D$. Let $\Theta,\Theta'$ be complex Hecke eigensystems over $K$ (a nonzero level ideal together with functions $a,b$ on the finite places) agreeing at all places outside some finite set. Let $R$ and $R'$ be smooth cuspidal realizations, at the production pins built from the carrier $D$, the level groups `levelOne` $N\sqcap$ `finiteAdelicGL2Subgroup`, the generators `heckeGen` and the box `adelicBox K`, of the raw central rescalings of $\Theta$ and $\Theta'$ (in which $b_v$ is replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$), and assume both realizing functions continuous. Then for every $\varepsilon>0$ in $[0,\infty]$ there are a finite set $s\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ and coefficients $l:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with $\int_D \lVert R'(y)-\sum_{h\in s} l(h)R(yh)\rVert^2\,d\mu < \varepsilon$, the integral being the lower Lebesgue integral for the adelic Haar measure `adelicGLHaar`.
--
--   This is strong multiplicity one together with multiplicity one for the cuspidal spectrum of $\mathrm{GL}_2$ over a number field, stated for realizing functions rather than for representations: a continuous cuspidal eigenfunction is approximated in mean square on the covering Siegel region by finite complex combinations of right translates of any other one with the same Hecke and central eigenvalues outside a finite set of places. It is used in the Langlands–Tunnell strand, where it feeds the transfer of archimedean holomorphy and weight-one behaviour between eigensystems agreeing away from finitely many places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
            (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε := by sorry
