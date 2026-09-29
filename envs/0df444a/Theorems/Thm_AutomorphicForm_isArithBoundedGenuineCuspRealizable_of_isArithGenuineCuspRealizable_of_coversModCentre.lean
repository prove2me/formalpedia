-- Prove2me | Theorems.Thm_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithGenuineCuspRealizable_of_coversModCentre
-- name    : AutomorphicForm.isArithBoundedGenuineCuspRealizable_of_isArithGenuineCuspRealizable_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/48b60e9b-478f-5ac8-8f11-f0ac8233e483
-- title:
--   Boundedness upgrade for cusp realizations on covering Siegel windows
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$, $0<d_1$ and $d_1<d_2$, and let $T$ be a finite set of points of $\mathrm{GL}_2$ over the adeles of $K$. Write $W=\bigcup_{x\in T}\{gx: g\in \mathfrak S\}$ for the union of the right translates by the elements of $T$ of the centre-cut Siegel set $\mathfrak S=$ `centreCutSiegelSet K c u d₁ d₂`, consisting of those adelic matrices whose finite part lies in `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $w$, $c\le$ `localHeight`, `xWindowSq` $\le u^2$, and `archDetNorm` $w\in[d_1,d_2]$. Assume `CoversModCentre K W`: every adelic $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and a central adelic scalar $z$ with $\gamma g z\in W$. Let $\Phi$ be a complex Hecke eigensystem for $K$ (a nonzero level ideal of $\mathcal O_K$ together with families $a,b$ indexed by the finite places), and let the pins be `productionPinsOf` over the window $W$, with level subgroups $N\mapsto$ `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, the Hecke generators `heckeGen (𝓞 K) K v`, full central subgroup, the adelic Haar measure on $\mathrm{GL}_2$ and the Haar measure on the adeles conditioned on `adelicBox K`. If the central rescaling $\Phi.\mathtt{toRawCentral}$ (same level and same $a$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$) is genuinely cusp-realizable at these pins, i.e. admits a smooth cusp realization at the pins with continuous underlying function, then it is boundedly genuinely cusp-realizable at the same pins relative to the standard additive character `StandardAddChar.stdAddChar K`: there is a smooth cusp realization at the pins for $\Phi.\mathtt{toRawCentral}$ satisfying `IsBoundedGenuineCuspRealizationAt` for that character.
--
--   This is the step upgrading a genuine cusp realization of a Hecke eigensystem to one with the analytic boundedness and Whittaker-integrability properties needed downstream, in the classical shape 'a cuspidal automorphic function smoothed by a test function is bounded on Siegel sets'. It feeds the base-change and Langlands–Tunnell constructions, being cited in the formal base-change statement for degrees two and three and in two Langlands–Tunnell existence statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArithBoundedGenuineCuspRealizable_of_isArithGenuineCuspRealizable_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.isArithBoundedGenuineCuspRealizable_of_isArithGenuineCuspRealizable_of_coversModCentre
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c)
    (hd₁ : 0 < d₁)
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Φ : HeckeEigensystem K ℂ)
    (hΦ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Φ) :
    IsArithBoundedGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (StandardAddChar.stdAddChar K) Φ := by sorry
