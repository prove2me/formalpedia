-- Prove2me | Theorems.Thm_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample
-- name    : AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/dedbbe1b-5693-5eb8-8e68-01e269e73050
-- title:
--   Strong multiplicity one on an ample Siegel window for GL₂
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2,\kappa$ be real numbers with $0<c$, $0<d_1$, $d_1<d_2$ and $1\le\kappa$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $\mathfrak{S}$ for `centreCutSiegelSetAmple K c u d₁ d₂ κ`, the set of $g$ lying in the centre-cut Siegel set `centreCutSiegelSet K c u d₁ d₂` whose archimedean heights are $\kappa$-comparable, i.e. $\mathrm{localHeight}$ of the $w$-component of the archimedean part of $g$ is at most $\kappa$ times that of the $w'$-component for all infinite places $w,w'$, and put $D=\bigcup_{x\in T}\mathfrak{S}x$. Assume $D$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,\mathrm{centralScalar}(z)\in D$. Let $\Theta,\Theta'$ be complex Hecke eigensystems for $K$ (a nonzero level ideal together with functions $a,b$ on the finite places) which agree away from a finite set of finite places, i.e. $a_v=a'_v$ and $b_v=b'_v$ for $v$ outside some finite set. Let $R$, $R'$ be smooth cuspidal realizations, at the production pins with window $D$, level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators `heckeGen` and adelic box `adelicBox`, of the raw central rescalings of $\Theta$ and $\Theta'$ (same level and same $a$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$); thus each is a nonzero function on $\mathrm{GL}_2(\mathbb{A}_K)$ with a central character on the full centre, smooth and cuspidal in the sense of `IsSmoothCuspAutomorphicFnAt`, invariant under the level subgroup, and an eigenfunction for the Hecke coset operators with eigenvalue $a_v$ and for the central scalars $\det(\mathrm{heckeGen}\,v)$ with eigenvalue the rescaled $b_v$, outside its own exceptional finite set. Assume moreover that both $R$ and $R'$ are genuine, i.e. their underlying functions are continuous. Then for every $\varepsilon\in[0,\infty]$ with $\varepsilon>0$ there are a finite set $s$ of elements of $\mathrm{GL}_2(\mathbb{A}_K)$ and coefficients $l:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ such that the lower Lebesgue integral of $\|R'(y)-\sum_{h\in s}l(h)R(yh)\|^2$ over $y\in D$, against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$, is less than $\varepsilon$.
--
--   This is strong multiplicity one together with multiplicity one for the cuspidal spectrum of $\mathrm{GL}_2$ over a number field, formulated for realizing functions rather than representations: two continuous cuspidal eigenfunctions with the same Hecke eigenvalues at almost all finite places approximate one another in mean square over the covering window by finite combinations of right translates. It is used in the identification of cusp constituents, [`AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre`](thm.html#AutomorphicForm.eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre), and in the variant [`AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre`](thm.html#AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre) in which the ample window hypothesis is removed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample
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
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u d₁ d₂ κ,
            (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε := by sorry
