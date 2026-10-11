-- Prove2me | Theorems.Thm_ConnesGreen_canonical_nested_diagonal_actual_tail_marker_recovery
-- name    : ConnesGreen.canonical_nested_diagonal_actual_tail_marker_recovery
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T17:56:05.094673+00:00
-- url     : https://prove2.me/theorems/e32617ea-8427-404a-a046-40848876c9d1
-- title:
--   Nested actual-zero cutoffs and uniform zero-floor diagonal marker approximation
-- statement:
--   Let $T>0$ be an upper support bound, let $S$ be a fixed finite set of actual critical-strip zeta zeros, and let $(K_n)$ be any prescribed sequence of finite actual-zero packets. Let $\mu_n>0$ and $0<\varepsilon_n<1$ be prescribed numerical schedules, both tending to zero. There exist nested finite reflection-closed sets $F_n$ containing $S$ and $K_n$, chosen before all support windows, regularizations, and tests. For every $n$ and every $0<t\le T$, the original positive columns outside $F_n$ admit a bounded synthesis $P_{n,t}$, with
--   $$
--   \|P_{n,t}P_{n,t}^*\|+\|R_{F_n,t}\|<\varepsilon_n.
--   $$
--   Here $R_{F_n,t}$ is the covariance of the original negative columns outside $F_n$. For every $\nu\ge\mu_n$,
--   $$
--   \|R_{F_n,t}\|\le\varepsilon_n\nu,\qquad
--   0\le M_{S,t}(L_t+\nu I)-M_{S,t}(L_t+\nu I-R_{F_n,t}),\qquad
--   \|M_{S,t}(L_t+\nu I)-M_{S,t}(L_t+\nu I-R_{F_n,t})\|\le\varepsilon_n.
--   $$
--   The restored operator $L_t+\nu I-R_{F_n,t}$ is nonnegative and invertible. Here $L_t$ is the original complete positive covariance, $N_{S,t}$ is the unchanged original selected negative synthesis, and $M_{S,t}(A)=(I+N_{S,t}^*A^{-1}N_{S,t})^{-1}$ uses the original total operator inverse. For every original smooth compactly supported test $g$ with support in $(-t,t)$ and original physical source norm squared at most $1$, the complete actual-zero norm tail is summable and satisfies
--   $$
--   \sum_{\rho\notin F_n}\left|m_\rho\widehat{(g*g^*)}(\rho)\right|<\varepsilon_n.
--   $$
--   The multiplicities and Mellin transform are those of the original actual zeta-zero development. For every tolerance $\delta>0$, one index $N$ makes the negative covariance norm, selected marker error, and complete actual norm tail less than $\delta$ for all $n\ge N$, all $0<t\le T$, all $\nu\ge\mu_n$, and all normalized original tests. This is uniform diagonal approximation by growing cutoffs. It does not exchange ordered limits or establish an arithmetic endpoint, quartet separation, or RH.
-- source:
--   Let $T>0$ be an upper support bound, let $S$ be a fixed finite set of actual critical-strip zeta zeros, and let $(K_n)$ be any prescribed sequence of finite actual-zero packets. Let $\mu_n>0$ and $0<\varepsilon_n<1$ be prescribed numerical schedules, both tending to zero. There exist nested finite reflection-closed sets $F_n$ containing $S$ and $K_n$, chosen before all support windows, regularizations, and tests. For every $n$ and every $0<t\le T$, the original positive columns outside $F_n$ admit a bounded synthesis $P_{n,t}$, with
--   $$
--   \|P_{n,t}P_{n,t}^*\|+\|R_{F_n,t}\|<\varepsilon_n.
--   $$
--   Here $R_{F_n,t}$ is the covariance of the original negative columns outside $F_n$. For every $\nu\ge\mu_n$,
--   $$
--   \|R_{F_n,t}\|\le\varepsilon_n\nu,\qquad
--   0\le M_{S,t}(L_t+\nu I)-M_{S,t}(L_t+\nu I-R_{F_n,t}),\qquad
--   \|M_{S,t}(L_t+\nu I)-M_{S,t}(L_t+\nu I-R_{F_n,t})\|\le\varepsilon_n.
--   $$
--   The restored operator $L_t+\nu I-R_{F_n,t}$ is nonnegative and invertible. Here $L_t$ is the original complete positive covariance, $N_{S,t}$ is the unchanged original selected negative synthesis, and $M_{S,t}(A)=(I+N_{S,t}^*A^{-1}N_{S,t})^{-1}$ uses the original total operator inverse. For every original smooth compactly supported test $g$ with support in $(-t,t)$ and original physical source norm squared at most $1$, the complete actual-zero norm tail is summable and satisfies
--   $$
--   \sum_{\rho\notin F_n}\left|m_\rho\widehat{(g*g^*)}(\rho)\right|<\varepsilon_n.
--   $$
--   The multiplicities and Mellin transform are those of the original actual zeta-zero development. For every tolerance $\delta>0$, one index $N$ makes the negative covariance norm, selected marker error, and complete actual norm tail less than $\delta$ for all $n\ge N$, all $0<t\le T$, all $\nu\ge\mu_n$, and all normalized original tests. This is uniform diagonal approximation by growing cutoffs. It does not exchange ordered limits or establish an arithmetic endpoint, quartet separation, or RH.
--
--   Native proof closes using the complete preceding uniform-band proof and the existing certified module closure. The original selected actor remains S at every stage. Enlarged seed packets are used only to choose the cutoff; their selected marker conclusions are discarded and marker stability is reapplied to S. No actual-zero enumeration, replacement zero model, arithmetic lower bound, project-specific axiom or admission is introduced. Native checkout head remains ada7948cb459fd21d400cd8f2a92e87672e31f2d, with no new commit or CI claim. Original RPB108 original-form attachments remain a separate future formalization task.

import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_nested_diagonal_actual_tail_marker_recovery
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (K : ℕ → Finset CriticalZeros) (μ ε : ℕ → ℝ)
    (hμ : ∀ n, 0 < μ n) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n < 1)
    (hμlim : Tendsto μ atTop (nhds 0)) (hεlim : Tendsto ε atTop (nhds 0)) :
    ∃ F : ℕ → Finset CriticalZeros, Monotone F ∧
      (∀ n, S ⊆ F n ∧ K n ⊆ F n ∧ (∀ τ ∈ F n, reflectedZero τ ∈ F n)) ∧
      (∀ n, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ (F n)}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht (F n)‖ < ε n ∧
          (∀ ν : ℝ, μ n ≤ ν →
            ‖canonicalTailCovariance t ht (F n)‖ ≤ ε n * ν ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n)) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ ≤ ε n) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
          ‖canonicalTailCovariance t ht (F n)‖ < δ ∧
          (∀ ν : ℝ, μ n ≤ ν → ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ < δ) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < δ)) := by sorry
