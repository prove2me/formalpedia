-- Prove2me | Theorems.Thm_ConnesGreen_canonical_negative_background_custody
-- name    : ConnesGreen.canonical_negative_background_custody
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T04:24:54.23198+00:00
-- url     : https://prove2.me/theorems/b0b8df0a-d262-461a-bc98-f553b6e5fe6e
-- title:
--   Complete actual-zero negative-background synthesis and exact covariance custody
-- statement:
--   Fix a positive support window $t$ and a finite packet $\Pi$ of actual nontrivial zeta zeros. In the previously certified physical Green Hilbert space, put $n_\rho=\tfrac12(\sqrt{m_\rho}v_\rho-\sqrt{m_{\rho^\sharp}}v_{\rho^\sharp})$, where $v_\rho$ is the original Green source realization and $\rho^\sharp=1-\overline\rho$. There are bounded synthesis maps $N$, $M$ and $B$ for all negative actors, the selected packet, and its complete complement, respectively. Their basis columns are exactly the supplied original actors, and the complement is uniquely determined by these columns. For every physical vector $h$,
--   $$ (B^*h)_\rho=\langle n_\rho,h\rangle\quad(\rho\notin\Pi),\qquad \|M^*h\|^2+\|B^*h\|^2=\|N^*h\|^2,$$
--   and the operator covariance splits exactly as
--   $$ NN^*=MM^*+BB^*,\qquad BB^*\ge0.$$
--   No unselected negative channel is discarded, and no reflection quotient or change of metric is made. This theorem constructs the background needed for the arithmetic marker-transfer target on the original actual-zero carrier. It does not assert a resolvent estimate, interchange endpoint limits, prove the half-threshold marker bound, or prove RH. Those arithmetic inequalities remain separate from operator custody.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/CanonicalGreenBackground.lean, based on repository commit b019d40205680f9761a4b0a80cbcad56ee1b606b. Exact incremental source and native audit are delivered in Connes_Weil_Green_Background_Custody.zip; the P2M proof reuses the existing canonical model and proved canonical Green realization.

import Definitions.Def_ConnesGreen_actual_pair_columns
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical

theorem ConnesGreen.canonical_negative_background_custody (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ∃ N : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
    ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, N (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ h ρ, (ContinuousLinearMap.adjoint B) h ρ =
        ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1, h⟫_ℂ) ∧
      (∀ h, ‖(ContinuousLinearMap.adjoint M) h‖ ^ 2 +
        ‖(ContinuousLinearMap.adjoint B) h‖ ^ 2 = ‖(ContinuousLinearMap.adjoint N) h‖ ^ 2) ∧
      N ∘L N.adjoint = M ∘L M.adjoint + B ∘L B.adjoint ∧
      (B ∘L B.adjoint).IsPositive ∧
      (∀ T : ℓ²({ρ : CriticalZeros // ρ ∉ S}, ℂ) →L[ℂ] Physical t,
        (∀ ρ, T (lp.single 2 ρ (1 : ℂ)) =
          negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) → T = B) := by sorry
