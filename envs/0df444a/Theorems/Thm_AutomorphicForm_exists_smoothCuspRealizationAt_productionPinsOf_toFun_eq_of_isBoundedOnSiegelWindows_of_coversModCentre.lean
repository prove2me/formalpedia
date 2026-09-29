-- Prove2me | Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre
-- name    : AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/333074f7-e4b1-5bee-8d0c-2532cb929ec4
-- title:
--   Transporting a cusp realization to Siegel-window production pins
-- statement:
--   Work over $F=\mathbb{Q}$, with $\mathrm{GL}_2$ of the adele ring, written `AdelicGL2 (𝓞 ℚ) ℚ`. Let $c,u,d_1,d_2$ be reals with $c>0$, $d_1>0$ and $d_1<d_2$, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet ℚ c u d₁ d₂` consists of those $g$ whose finite component lies in the integral subgroup `finiteIntegralGL2`, whose archimedean component has local height at least $c$ at every infinite place, has $x$-window square at most $u^2$ there, and whose archimedean determinant norm lies in $[d_1,d_2]$ at every infinite place. Assume `CoversModCentre ℚ D`, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and $z\in\mathbb{A}_{\mathbb{Q}}^\times$ with $\gamma g z\in D$ (images under `globalPoints` and `centralScalar`). Let $\Phi$ be a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal together with families $a_v,b_v$ indexed by the height-one primes of $\mathbb{Z}$), let $R$ be a smooth cusp realization of $\Phi$ at the pins `productionPinsGeneral ℚ`, assume $R$ is genuine, that is `R.toFun` is continuous, and assume `IsBoundedOnSiegelWindows ℚ R.toFun`: for all parameters $c',u',d_1',d_2'$ with $c'>0$, $d_1'>0$ and every finite $T'$, the function `R.toFun` is bounded in norm on the corresponding finite union of right translates of the centre-cut Siegel set. Then there exists a smooth cusp realization $R'$ of $\Phi$ at the pins `productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)` — Borel structure and Haar measure on $\mathrm{GL}_2$, window $D$, full central subgroup, the indicated level subgroups and Hecke generators, and the adele-box conditional measure — with $R'.toFun = R.toFun$.
--
--   This is the window-transport step in the adelic set-up: it moves a realization of a Hecke eigensystem from the general production pins to the pins attached to a prescribed finite union $D$ of translates of a centre-cut Siegel set, keeping the underlying function unchanged. It is used in the construction of a genuine cusp realization with prescribed newvector conductor attached to a primitive weight-one form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre.lean

import Mathlib
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ)
    (hR : IsGenuineCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ R)
    (hb : IsBoundedOnSiegelWindows ℚ R.toFun) :
    ∃ R' : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Φ,
      R'.toFun = R.toFun := by sorry
