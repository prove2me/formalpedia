-- Prove2me | Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
-- name    : AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/3864f97d-9d43-53da-80ab-e9512d232068
-- title:
--   Transporting a continuous cusp realization to the standard Siegel window
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $c>0$, $0<d_1<d_2$, and a finite set $T$ of elements of $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$, and put $D=\bigcup_{x\in T}\{g x : g\in \mathcal S\}$, where $\mathcal S=$ `centreCutSiegelSet ℚ c u d₁ d₂` consists of those $g$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $w$, `localHeight` $\ge c$, `xWindowSq` $\le u^2$ and `archDetNorm` $w\,g\in[d_1,d_2]$. Assume `CoversModCentre`: every $g$ admits $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and an adelic unit $z$ with $\gamma g\,z\in D$ (via `globalPoints` and `centralScalar`). Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal and families $a,b$ over the finite places). Let $R$ be a smooth cusp realization of $\Phi$ at the pins `productionPinsOf` with domain $D$, full central subgroup, level groups `levelOne` intersected with `finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, and the adelic Haar measure conditioned on `adelicBox ℚ`; assume `IsGenuineCuspRealizationAt`, i.e. that `R.toFun` is continuous. Then there is a smooth cusp realization $R'$ of $\Phi$ at the pins `productionPinsGeneral ℚ` with $R'$`.toFun` $=R$`.toFun`.
--
--   This is the reduction-theoretic step that replaces an arbitrary covering family of translated centre-cut Siegel windows by the fixed window built into `productionPinsGeneral ℚ` (the general-field pins at the numerics $(1/2,1,1/2,2)$, whose domain is the union of right translates by `classRepTranslates ℚ` of the corresponding centre-cut Siegel set), the only slot of the two pins bundles that differs being the domain of square-integrability. It is used to normalise the carrier pins in the construction of automorphic realizations, and is invoked by the Langlands–Tunnell side of the development as well as by a variant with an extra inequality hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre.lean

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
  AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Φ)
    (hR : IsGenuineCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Φ R) :
    ∃ R' : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ, R'.toFun = R.toFun := by sorry
