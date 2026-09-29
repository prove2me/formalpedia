-- Prove2me | Theorems.Thm_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample_principal
-- name    : AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/0ab17c99-bfa6-5011-9275-efb0bc7611e8
-- title:
--   Mean-square strong multiplicity one on an ample Siegel window
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2,\kappa$ be real numbers with $d_1<d_2$, $1\le\kappa$, $0<c$ and $0<d_1$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $\mathfrak{S}$ for `centreCutSiegelSetAmple K c u d₁ d₂ κ`, the set of $g$ lying in `centreCutSiegelSet K c u d₁ d₂` whose archimedean component has comparable local heights, $\mathrm{localHeight}$ at any infinite place $w$ being at most $\kappa$ times the one at any infinite place $w'$, and put $D=\bigcup_{x\in T}\mathfrak{S}x$. Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z\in D$. Let $\Theta,\Theta'$ be complex Hecke eigensystems over $K$ (a nonzero level ideal together with $a,b$ on the finite places) agreeing away from a finite set of finite places, i.e. $\Theta.a\,v=\Theta'.a\,v$ and $\Theta.b\,v=\Theta'.b\,v$ outside a finite set. Let $R$, $R'$ be smooth cuspidal realizations, at the production pins with window $D$, full central subgroup, levels $\Gamma(N)\cap\ker(\mathrm{glArch})$, Hecke generators `heckeGen`, and box `adelicBox K`, of the raw central rescalings of $\Theta$ and $\Theta'$ (same level and $a$, with $b\,v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b\,v$), and assume $R.\mathrm{toFun}$ and $R'.\mathrm{toFun}$ are continuous. Then for every $\varepsilon\in[0,\infty]$ with $\varepsilon>0$ there are a finite set $s$ of elements of $\mathrm{GL}_2(\mathbb{A}_K)$ and coefficients $l:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with $$\int^-_{y\in D}\bigl\|R'.\mathrm{toFun}(y)-\sum_{h\in s}l(h)\,R.\mathrm{toFun}(yh)\bigr\|^2\,d\mu<\varepsilon,$$ the lower Lebesgue integral being taken against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is strong multiplicity one for the cuspidal spectrum of $\mathrm{GL}_2$ over a number field, in the quantitative form of an $L^2$ approximation on the ample Siegel window $D$: each realizing function is a mean-square limit of finite combinations of right translates of the other as soon as the two eigensystems agree at all but finitely many finite places. It feeds the identification of cuspidal constituents at principal congruence level in [`AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre`](thm.html#AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_principal_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample_principal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample_principal
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hκ : 1 ≤ κ)
    (hc : 0 < c)
    (hd₁ : 0 < d₁)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ,
            (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε := by sorry
