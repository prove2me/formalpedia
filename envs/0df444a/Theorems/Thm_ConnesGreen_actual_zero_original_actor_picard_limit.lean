-- Prove2me | Theorems.Thm_ConnesGreen_actual_zero_original_actor_picard_limit
-- name    : ConnesGreen.actual_zero_original_actor_picard_limit
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T13:13:49.013038+00:00
-- url     : https://prove2.me/theorems/5e44f430-36e0-4991-a548-864f08326521
-- title:
--   Original actual-zero packet actors have their Picard marker norm limit
-- statement:
--   For $t>0$ and a finite selected packet $S$ of actual nontrivial zeta zeros, the original Green carrier $H_t$ has bounded full-positive and selected-negative syntheses $P,M$ with exactly the original basis columns, including analytic multiplicities, reflection duplication and pair normalization. On the same selected coefficient space, there is a positive contraction $G_0$ such that
--   $$G_0=\inf_{\varepsilon>0}(I+M^*(PP^*+\varepsilon I)^{-1}M)^{-1},\qquad\lim_{\varepsilon\downarrow0}\|(I+M^*(PP^*+\varepsilon I)^{-1}M)^{-1}-G_0\|=0.$$
--   The full-positive synthesis retains all actual zeros. Finite dimensionality is established for the original selected coefficient space by its coordinate injection. No original actor, zero set or physical metric is replaced, and no arithmetic endpoint lower bound or RH is assumed.
-- source:
--   monocap-tech/weil at native base b019d40205680f9761a4b0a80cbcad56ee1b606b; new Screening/MarkerLimit.lean and Connes/CanonicalGreenMarkerLimit.lean. Exact certified sources in Connes_Weil_Original_Picard_Limit.zip. The inner norm limit is proved; critical support location, outer endpoint transfer and unconditional RH are not asserted.

import Definitions.Def_ConnesGreen_actual_pair_columns
import Definitions.Def_WeilMarker_regularized_cost
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability Filter Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology

theorem ConnesGreen.actual_zero_original_actor_picard_limit (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) :
    ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      ∃ G₀ : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ),
        0 ≤ G₀ ∧ G₀ ≤ 1 ∧
        IsGLB ((fun ε : ℝ => marker (P ∘L P.adjoint + ε • 1) M) '' Ioi 0) G₀ ∧
        Tendsto (fun ε : ℝ => marker (P ∘L P.adjoint + ε • 1) M)
          (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds G₀) := by sorry
