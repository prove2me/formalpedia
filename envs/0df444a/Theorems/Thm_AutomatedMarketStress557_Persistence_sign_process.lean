-- Prove2me | Theorems.Thm_AutomatedMarketStress557_Persistence_sign_process
-- name    : AutomatedMarketStress557.Persistence.sign_process
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:07.354124+00:00
-- url     : https://prove2.me/theorems/24ecf11c-0b6e-4c81-91d0-fbada753596a
-- title:
--   Lemma 4.1 — The sign process
-- statement:
--   Let $P$ be a probability measure, $\nu$ the news probability law with CDF $G$, and let the independent news and fair initial sign satisfy Assumption 1. For $s>0$ and any $\beta\in\mathbb R$, generate $r_t=\beta D_{t-1}+s\xi_t$ and $D_t=\operatorname{sgn}(r_t)$. Put $A_t=D_tD_{t-1}$ and $q=G(\beta/s)$. Then the entire family $(A_t)_{t\ge1}$ is independent and identically distributed, independent jointly of $D_0$, and
--
--   $$P(A_t=1)=q.$$
--
--   The sign process is a stationary symmetric Markov chain with fair marginals. Its full trajectory law is invariant under time shifts and simultaneous sign reversal. For every finite sign history $a_0,\ldots,a_n\in\{-1,+1\}$ and next sign $b\in\{-1,+1\}$,
--
--   $$P(D_0=a_0,\ldots,D_n=a_n,D_{n+1}=b)=P(D_0=a_0,\ldots,D_n=a_n)\begin{cases}q,&b=a_n,\\1-q,&b\ne a_n.\end{cases}$$
--
--   This identifies the serial structure of the actual recursion and supplies the source's sole numbered dependency for the mixture-law result. Sign agreement, rather than a change of sign, is the event $A_t=+1$.
--
--   Differences from the source:
--   - encoding: an arbitrary initial return with fair sign, and news indexed from 1 → the initial sign alone is stored at time zero, and news index n denotes source time n+1; reason: the recursion uses only the initial sign and this reindexing preserves every positive-time trajectory.
--   - encoding: an unspecified sign at zero → sign(0)=+1; reason: continuous news makes every positive-time zero return null, explicitly established by the goal theorem, so this convention changes no law.
--   - encoding: a stationary symmetric Markov chain → whole-trajectory law invariance and the finite-history transition identity; reason: on the two sign states these express the full stationary symmetric Markov assertion without conditioning on null histories.
-- source:
--   Irene Aldridge, STOC 2027 submission #557 (October 2026), Lemma 4.1, PDF p. 3; equation (3), PDF p. 2; Assumption 1, PDF p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/557.pdf

import Mathlib
import Definitions.Def_AutomatedMarketStress557_Persistence_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AutomatedMarketStress557.Persistence

/-- Lemma 4.1 (The sign process), Irene Aldridge, STOC 2027 submission #557
(October 2026), PDF p. 3. The transition assertion uses all finite sign histories,
so it is the full Markov property, not just a two-time transition frequency.
Stationarity and sign symmetry are equalities of laws of entire trajectories. -/
theorem sign_process {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) (hM : Model P ν d₀ ξ)
    (β s : ℝ) (hs : 0 < s) :
    iIndepFun (flips β s d₀ ξ) P ∧
    (∀ i j : ℕ, IdentDistrib (flips β s d₀ ξ i) (flips β s d₀ ξ j) P P) ∧
    (∀ n : ℕ, P.real {ω | flips β s d₀ ξ n ω = 1} = cdf ν (β / s)) ∧
    IndepFun (fun ω n => flips β s d₀ ξ n ω) d₀ P ∧
    (∀ t : ℕ, HasLaw (signs β s d₀ ξ t) fairSignLaw P) ∧
    (∀ k : ℕ, IdentDistrib (fun ω n => signs β s d₀ ξ (n + k) ω)
      (fun ω n => signs β s d₀ ξ n ω) P P) ∧
    IdentDistrib (fun ω n => -signs β s d₀ ξ n ω)
      (fun ω n => signs β s d₀ ξ n ω) P P ∧
    (∀ (n : ℕ) (a : ℕ → ℝ) (b : ℝ),
      (∀ i : ℕ, i ≤ n → a i = -1 ∨ a i = 1) → (b = -1 ∨ b = 1) →
      P {ω | (∀ i : ℕ, i ≤ n → signs β s d₀ ξ i ω = a i) ∧
        signs β s d₀ ξ (n + 1) ω = b} =
      P {ω | ∀ i : ℕ, i ≤ n → signs β s d₀ ξ i ω = a i} *
        ENNReal.ofReal (if b = a n then cdf ν (β / s) else 1 - cdf ν (β / s))) := by sorry

end AutomatedMarketStress557.Persistence
