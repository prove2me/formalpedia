-- Prove2me | Theorems.Thm_AutomatedMarketStress557_Persistence_volatility_equivalence_persistence_separation
-- name    : AutomatedMarketStress557.Persistence.volatility_equivalence_persistence_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:54.631714+00:00
-- url     : https://prove2.me/theorems/4ce5057a-947a-4952-937d-e324f1175a7b
-- title:
--   Theorem 4.2 — Volatility equivalence, persistence separation
-- statement:
--   Let $P$ be a probability measure and let the news law $\nu$ have continuous, strictly increasing, zero-symmetric CDF $G$ on all of $\mathbb R$. The news $(\xi_t)_{t\ge1}$ is iid with law $\nu$ and independent of the fair initial sign $D_0$. For $s>0$, generate $r_t=\beta D_{t-1}+s\xi_t$ for every real $\beta$. For $c\ge0$, let $L_j$ be the successive actual maximal runs of $r_t<-c$, scanned from period 1, and let $m_j(\beta,s,c)=E[L_j]$.
--
--   1. For every $t\ge1$, the law of $r_t$ is the equal mixture of the laws of $\beta+s\xi_1$ and $-\beta+s\xi_1$, with CDF
--
--      $$P(r_t\le x)=\tfrac12G((x-\beta)/s)+\tfrac12G((x+\beta)/s).$$
--
--      It depends on $\beta$ only through $|\beta|$. If $\xi_1$ has finite second moment, then $r_t$ does too and $\operatorname{Var}(r_t)=\beta^2+s^2\operatorname{Var}(\xi_1)$. Every zero-return event is null. The stress frequency is
--
--      $$F_t(\beta)=\tfrac12[G((-c-\beta)/s)+G((\beta-c)/s)]=F_t(-\beta).$$
--
--   2. Almost surely every episode entry and exit exists at finite time, and every length is a positive finite integer. The entire length sequence is iid geometric on $\{1,2,\ldots\}$: for every $j,k\ge0$, with $p=G((c-\beta)/s)\in(0,1)$,
--
--      $$P(L_j>k)=G((\beta-c)/s)^k,\quad P(L_j=k+1)=p\,G((\beta-c)/s)^k,\quad m_j(\beta,s,c)=\frac1{G((c-\beta)/s)}.$$
--
--      The extended expectation is finite and equals this same reciprocal. For each fixed $G,s,c,j$, $m_j$ is strictly increasing in $\beta$ on all of $\mathbb R$.
--
--   3. For every $\beta>0$, $c\ge0$, and episode $j$,
--
--      $$\frac{m_j(\beta,s,c)}{m_j(-\beta,s,c)}=\frac{G((c+\beta)/s)}{G((c-\beta)/s)}>1.$$
--
--      For every fixed $a=c/s\ge0$, both $G(a+u)/G(a-u)$ and the operational mean ratio $m_j(su,s,sa)/m_j(-su,s,sa)$ tend to $+\infty$ as $u=\beta/s\to+\infty$.
--
--   This gives identical complete return marginals under opposite feedback, while retaining different serial stress persistence at every threshold. The variance clause imposes no moment condition on the other conclusions. The geometric and mean assertions concern the scanned episodes, not an assumed geometric surrogate or a length-biased observation.
--
--   Differences from the source:
--   - encoding: an arbitrary initial return with fair sign, and news indexed from 1 → the initial sign alone is stored at time zero, and news index n denotes source time n+1; reason: the recursion uses only the initial sign and this reindexing preserves every positive-time trajectory.
--   - encoding: an unspecified sign at zero → sign(0)=+1 and an explicit zero-return null-event conclusion; reason: continuity of the news CDF makes the choice immaterial to all laws.
--   - encoding: maximal stress runs and their expectations → successive entries scanned from period 1, extended-natural lengths with infinity on missing entries or exits, and nonnegative extended integrals proved finite before real conversion; reason: Assumption 1 specifies only the initial sign, so no initial-magnitude stress or prehistory is introduced, and the theorem certifies existence, termination and finite means rather than assuming them.
--   - encoding: finite variance of the news → the local hypothesis MemLp of the first news variable with exponent 2; reason: on a real probability space finite second moment is the standard finite-variance condition, and it is used only for the variance implication.
--   - reading: the ratio tends to infinity as beta/s tends to infinity, with other parameters unstated → G and a=c/s are fixed while u=beta/s tends to infinity, for every a≥0; reason: the source proof says numerator tends to 1 and denominator to 0; unrestricted joint variation is false, for Gaussian G with c=1, beta=1/2 and s=1/n the ratio tends to 1 although beta/s tends to infinity.
-- source:
--   Irene Aldridge, STOC 2027 submission #557 (October 2026), Theorem 4.2(1)–(3), PDF p. 3; equation (3), PDF p. 2; Assumption 1 and Definition 3.1, PDF p. 3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/557.pdf

import Mathlib
import Definitions.Def_AutomatedMarketStress557_Persistence_episodeLength

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace AutomatedMarketStress557.Persistence

/-- Theorem 4.2, all parts (1)--(3), Irene Aldridge, STOC 2027 submission #557
(October 2026), PDF p. 3. The limit holds with G and a = c/s fixed, as indicated
by the proof's numerator → 1 and denominator → 0. News index 0 is ξ_1.
Actual runs are scanned from period 1; the arbitrary initial magnitude is unused.
Finite variance is local to its own implication; no global moment restriction. -/
theorem volatility_equivalence_persistence_separation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (d₀ : Ω → ℝ) (ξ : ℕ → Ω → ℝ) (hM : Model P ν d₀ ξ)
    (s : ℝ) (hs : 0 < s) :
    (∀ (β : ℝ) (t : ℕ), 1 ≤ t →
      HasLaw (returns β s d₀ ξ t) (marginalMixture ν β s) P ∧
      (∀ x : ℝ, cdf (Measure.map (returns β s d₀ ξ t) P) x =
        (1 / 2 : ℝ) * cdf ν ((x - β) / s) +
        (1 / 2 : ℝ) * cdf ν ((x + β) / s)) ∧
      Measure.map (returns β s d₀ ξ t) P = Measure.map (returns (-β) s d₀ ξ t) P ∧
      Measure.map (returns β s d₀ ξ t) P = Measure.map (returns |β| s d₀ ξ t) P ∧
      (MemLp (ξ 0) 2 P → MemLp (returns β s d₀ ξ t) 2 P ∧
        variance (returns β s d₀ ξ t) P = β ^ 2 + s ^ 2 * variance (ξ 0) P) ∧
      P {ω | returns β s d₀ ξ t ω = 0} = 0 ∧
      (∀ c : ℝ, 0 ≤ c →
        P.real {ω | returns β s d₀ ξ t ω < -c} =
          (1 / 2 : ℝ) * (cdf ν ((-c - β) / s) + cdf ν ((β - c) / s)) ∧
        P.real {ω | returns β s d₀ ξ t ω < -c} =
          P.real {ω | returns (-β) s d₀ ξ t ω < -c})) ∧
    (∀ β c : ℝ, 0 ≤ c →
      0 < cdf ν ((c - β) / s) ∧ cdf ν ((c - β) / s) < 1 ∧
      (∀ᵐ ω ∂P, ∀ j : ℕ,
        episodeEntry (fun t => returns β s d₀ ξ t ω) c j < ⊤ ∧
        episodeExit (fun t => returns β s d₀ ξ t ω) c j < ⊤ ∧
        1 ≤ episodeLength (fun t => returns β s d₀ ξ t ω) c j ∧
        episodeLength (fun t => returns β s d₀ ξ t ω) c j < ⊤) ∧
      iIndepFun (fun j ω => episodeLength (fun t => returns β s d₀ ξ t ω) c j) P ∧
      (∀ i j : ℕ, IdentDistrib
        (fun ω => episodeLength (fun t => returns β s d₀ ξ t ω) c i)
        (fun ω => episodeLength (fun t => returns β s d₀ ξ t ω) c j) P P) ∧
      (∀ j k : ℕ,
        P.real {ω | (k : ℕ∞) < episodeLength (fun t => returns β s d₀ ξ t ω) c j} =
          cdf ν ((β - c) / s) ^ k ∧
        P.real {ω | episodeLength (fun t => returns β s d₀ ξ t ω) c j =
          ((k + 1 : ℕ) : ℕ∞)} =
          cdf ν ((c - β) / s) * cdf ν ((β - c) / s) ^ k) ∧
      (∀ j : ℕ,
        AEMeasurable (fun ω => lengthValue
          (episodeLength (fun t => returns β s d₀ ξ t ω) c j)) P ∧
        extendedMeanLength P β s c d₀ ξ j < ⊤ ∧
        extendedMeanLength P β s c d₀ ξ j = ENNReal.ofReal (1 / cdf ν ((c - β) / s)) ∧
        meanLength P β s c d₀ ξ j = 1 / cdf ν ((c - β) / s))) ∧
    (∀ c : ℝ, 0 ≤ c → ∀ j : ℕ, StrictMono (fun β : ℝ => meanLength P β s c d₀ ξ j)) ∧
    (∀ β c : ℝ, 0 < β → 0 ≤ c → ∀ j : ℕ,
      meanLength P β s c d₀ ξ j / meanLength P (-β) s c d₀ ξ j =
        cdf ν ((c + β) / s) / cdf ν ((c - β) / s) ∧
      1 < meanLength P β s c d₀ ξ j / meanLength P (-β) s c d₀ ξ j) ∧
    (∀ a : ℝ, 0 ≤ a →
      Tendsto (fun u : ℝ => cdf ν (a + u) / cdf ν (a - u)) atTop atTop ∧
      ∀ j : ℕ, Tendsto (fun u : ℝ =>
        meanLength P (s * u) s (s * a) d₀ ξ j /
        meanLength P (-(s * u)) s (s * a) d₀ ξ j) atTop atTop) := by sorry

end AutomatedMarketStress557.Persistence
