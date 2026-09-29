-- Prove2me | Theorems.Thm_AutomorphicForm_coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
-- name    : AutomorphicForm.coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/004e06fc-1cd8-5d6c-b97c-f01ffde41ba1
-- title:
--   Raising the lower determinant bound of a centre-cut Siegel window
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2,d_1'$ be real numbers, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adele ring of $K$. For a real parameter $t$ write $W(t)=\bigcup_{x\in T}\{g x : g\in S(c,u,t,d_2)\}$, where $S(c,u,t,d_2)$ is the centre-cut Siegel set of those adelic matrices whose finite component lies in the integral subgroup `finiteIntegralGL2`, whose component at each infinite place $w$ has local height $\|\det\|/\mathrm{rowNormSq}$ at least $c$ and window coordinate `xWindowSq` at most $u^2$, and whose archimedean determinant norm `archDetNorm` at each $w$ lies in the closed interval $[t,d_2]$. Assume $d_1\le d_1'<d_2$; assume `CoversModCentre` for $W(d_1)$, that is, every adelic $g$ can be moved into $W(d_1)$ by left multiplication by a point of $\mathrm{GL}_2(K)$ and right multiplication by a central adelic scalar. Let $\Phi$ be a complex Hecke eigensystem of $K$ (a nonzero level ideal together with families $a,b$ indexed by the finite places) and assume `IsArithGenuineCuspRealizable` at the production pins over $W(d_1)$ — the carrier pins with Borel structure and adelic Haar measure on $\mathrm{GL}_2$, integration domain $W(d_1)$, full central subgroup, level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap$ `finiteAdelicGL2Subgroup`, Hecke generators $v\mapsto \mathrm{heckeGen}(v)$, and the adelic additive Haar measure conditioned on `adelicBox` — i.e. existence of a genuine smooth cusp realization at those pins for the raw central rescaling of $\Phi$ (same level and $a$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$). Then both conclusions hold for $W(d_1')$: `CoversModCentre` for $W(d_1')$, and `IsArithGenuineCuspRealizable` for $\Phi$ at the production pins built in the same way over $W(d_1')$.
--
--   This is a bookkeeping step in the adelic Siegel-set set-up: the determinant window is tightened from below, the new window being contained in the old one since $[d_1',d_2]\subseteq[d_1,d_2]$, while the covering property modulo the centre and genuine cusp-realizability of a fixed Hecke eigensystem at the associated production pins are retained. It is used by the statements on base change, twisting and agreement of eigensystems away from a finite set of places, which need the two properties for a window with a prescribed lower determinant bound.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hle : d₁ ≤ d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Φ : HeckeEigensystem K ℂ)
    (hΦ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Φ) :
    CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁' d₂) ∧
      IsArithGenuineCuspRealizable K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁' d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) Φ := by sorry
