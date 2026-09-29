-- Prove2me | Theorems.Thm_AutomorphicForm_isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_translate_sq_lt
-- name    : AutomorphicForm.isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_translate_sq_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/9d3335b2-7511-5754-8e5c-b3657a857dd2
-- title:
--   Holomorphy at a real place under L²-approximation by translates
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{x\in T} \{g x : g\in S\}$, where $S$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$: those $g$ whose finite part lies in `finiteIntegralGL2`, with $c\le$ the local height of the archimedean component at every infinite place, with `xWindowSq` of that component at most $u^2$, and with `archDetNorm` at every infinite place in $[d_1,d_2]$. Assume `CoversModCentre`: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ admits $\gamma\in\mathrm{GL}_2(K)$ and a central adelic scalar $z$ with $\gamma g z\in D$. Let $\xi$ be a character of the group $Z=\top$ of the production pins attached to $D$, the level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` and the box `adelicBox`. Let $\varphi,\varphi':\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous and both smooth cuspidal automorphic at those pins with character $\xi$ (i.e. cuspidal automorphic at the pins together with `IsKfSmooth`). Let $w$ be a real infinite place; assume $\varphi$ and $\varphi'$ both transform under `rowIsometrySubgroup₀` of $w$'s completion by the weight-one character `archWeightOneAt hw`, and that $\varphi$ is archimedean-holomorphic at $w$. Assume finally that for every $\varepsilon>0$ in $[0,\infty]$ there are a finite set $s$ of adelic matrices and coefficients $l$ with $\int_D \|\varphi'(y)-\sum_{h\in s} l(h)\varphi(yh)\|^2\,d\mu<\varepsilon$ for the adelic Haar measure $\mu$ on $\mathrm{GL}_2(\mathbb{A}_K)$. Then $\varphi'$ is archimedean-holomorphic at $w$: for every $g$, the function $z\mapsto (\operatorname{Im} z)^{-1}\varphi'\bigl(g\cdot\iota_w(\mathrm{iwasawaSectionGL}\,z)\bigr)$ is differentiable on the upper half-plane.
--
--   This is the archimedean $K$-type rigidity step in the weight-one setting: holomorphy at a real place is inherited by any function that can be approximated in $L^2$ over a covering Siegel window by finite linear combinations of right translates of a holomorphic weight-one form. It is used in the Langlands–Tunnell input, in the deduction that a function agreeing with a holomorphic weight-one form away from finitely many places is itself holomorphic at the real place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_translate_sq_lt.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem AutomorphicForm.isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_translate_sq_lt
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (φ φ' : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφc : IsSmoothCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      ξ φ)
    (hφ'c : IsSmoothCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      ξ φ')
    (w : InfinitePlace K) (hw : w.IsReal)
    (hφw : HasArchCharacterAt₀ K w (archWeightOneAt hw) φ)
    (hφhol : IsArchHolomorphicAt w hw φ)
    (hφ'w : HasArchCharacterAt₀ K w (archWeightOneAt hw) φ')
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
            (‖φ' y - ∑ h ∈ s, l h * φ (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε) :
    IsArchHolomorphicAt w hw φ' := by sorry
