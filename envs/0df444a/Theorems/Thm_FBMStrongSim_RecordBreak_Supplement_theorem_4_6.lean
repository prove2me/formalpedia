-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_Supplement_theorem_4_6
-- name    : FBMStrongSim.RecordBreak.Supplement.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:31:22.940807+00:00
-- url     : https://prove2.me/theorems/098fc315-ba47-43e1-b867-80815a71b626
-- title:
--   Theorem 4.6 — Correct acceptance and next-record law
-- statement:
--   Let $0<H<1$, $0<\delta<H$, $\rho>0$, and $n\ge N^*(\rho,\delta)$. For almost every realized level-$n$ input satisfying BCE, let $P_n=\kappa_n(x)$ and let $Q_n$ be the output law constructed by Algorithms 3–4. It is a probability measure, its acceptance indicator $I$ is Boolean, and
--   $$Q_n(I=1)=P_n(\tau<\infty),\qquad Q_n(M=m,I=1)=P_n(\tau=n+m)\quad(m\ge1).$$
--   Here $\tau$ is the first strict record level after $n$, and the events are computed from the dyadic path. These are both the Bernoulli success law and the joint law asserted by the source.
--
--   Differences from the source:
--   - encoding: P_n(·)=P(·|B_n) at realized input values → condDistrib evaluated at levelValues B n ω, with the conditional conclusions for P-almost every ω; reason: regular conditional laws are specified only almost everywhere; the kernel is computed from B and P
--   - generalization: the continuous fBM version → every process satisfying the published IsFBM coordinate-law model, without a path-continuity premise in Section 4; reason: these algorithm laws use only the countable dyadic coordinates, whose joint law agrees with the continuous version; no source process is excluded
--   - encoding: Algorithm 4 samples a finite augmented path → algorithmLaw samples a latent full dyadic completion and outputs only augmentedValues; reason: the exponential density factor depends only on the selected three coordinates, so restriction has exactly the algorithm marginal
--   - reading: the density ψ and the plus sign in the first displayed line defining Θ− (pp. 17–18) → measure tilting, with the negative signed parameter for Θ−; reason: known dyadic endpoints can make the Gaussian singular; the negative-tilt second line of the source fixes the sign
--   - encoding: I is Bernoulli with the stated parameter → I is the indicator of Accepted, Q is a probability measure, and the success probability is specified; reason: a Boolean indicator with this success mass has exactly that Bernoulli law
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 21, Theorem 4.6

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_SamplingModel

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Theorem 4.6 (p.21), success law and joint next-level law. -/
theorem theorem_4_6 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H delta rho : ℝ} (hH0 : 0 < H) (hH1 : H < 1) (hd0 : 0 < delta)
    (hdH : delta < H) (hrho : 0 < rho) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    (n : ℕ) (hn : startLevel rho delta ≤ n) :
    ∀ᵐ ω ∂P, let mu := conditionalLaw B P n (levelValues B n ω)
      let Q := algorithmLaw mu rho H delta n
      BCE mu rho H delta n →
        IsProbabilityMeasure Q ∧
        Q {z | Accepted mu rho H delta n z} = mu {v | ∃ m, FirstRecord rho H delta n m v} ∧
        ∀ m : ℕ, 1 ≤ m →
          Q {z | z.1 = m ∧ Accepted mu rho H delta n z} =
            mu {v | FirstRecord rho H delta n m v} := by sorry

end FBMStrongSim.RecordBreak.Supplement
