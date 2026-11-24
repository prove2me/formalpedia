-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_Supplement_theorem_4_7
-- name    : FBMStrongSim.RecordBreak.Supplement.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:32:03.046396+00:00
-- url     : https://prove2.me/theorems/d905c0ff-a266-4118-ad6c-943611e98df6
-- title:
--   Theorem 4.7 — Accepted augmented-path law
-- statement:
--   Under $0<H<1$, $0<\delta<H$, $\rho>0$, $n\ge N^*(\rho,\delta)$, and BCE at the realized input, write $\mathrm{AP}$ for the values output on $D_{n+m}\setminus D_n$. Almost surely with respect to the original fBM input, for every $m\ge1$ and measurable set $A$ of augmented-path values,
--   $$Q_n(\mathrm{AP}\in A\mid M=m,I=1)=P_n(\mathrm{AP}\in A\mid\tau=n+m).$$
--   The equality identifies the whole finite-dimensional output distribution, not just each coordinate separately. It is a companion theorem about the same rejection sampler.
--
--   Differences from the source:
--   - encoding: P_n(·)=P(·|B_n) at realized input values → condDistrib evaluated at levelValues B n ω, with the conditional conclusions for P-almost every ω; reason: regular conditional laws are specified only almost everywhere; the kernel is computed from B and P
--   - generalization: the continuous fBM version → every process satisfying the published IsFBM coordinate-law model, without a path-continuity premise in Section 4; reason: these algorithm laws use only the countable dyadic coordinates, whose joint law agrees with the continuous version; no source process is excluded
--   - encoding: Algorithm 4 samples a finite augmented path → algorithmLaw samples a latent full dyadic completion and outputs only augmentedValues; reason: the exponential density factor depends only on the selected three coordinates, so restriction has exactly the algorithm marginal
--   - reading: the density ψ and the plus sign in the first displayed line defining Θ− (pp. 17–18) → measure tilting, with the negative signed parameter for Θ−; reason: known dyadic endpoints can make the Gaussian singular; the negative-tilt second line of the source fixes the sign
--   - reading: the hypotheses implicit in the proof of Theorem 4.7 → n≥N* and BCE, as in Theorem 4.6; reason: p. 21 says both correctness theorems are under BCE and the proof of 4.7 invokes 4.6
--   - encoding: conditional probability on an event → Mathlib cond, returning zero on a null event; reason: Theorem 4.6 equates the conditioning-event masses; thus both sides have the same null-event convention
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 23, Theorem 4.7

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Supplement_SamplingModel

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Theorem 4.7 (p.23), conditional law on all measurable augmented-path sets. -/
theorem theorem_4_7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H delta rho : ℝ} (hH0 : 0 < H) (hH1 : H < 1) (hd0 : 0 < delta)
    (hdH : delta < H) (hrho : 0 < rho) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    (n : ℕ) (hn : startLevel rho delta ≤ n) :
    ∀ᵐ ω ∂P, let mu := conditionalLaw B P n (levelValues B n ω)
      let Q := algorithmLaw mu rho H delta n
      BCE mu rho H delta n → ∀ m : ℕ, 1 ≤ m →
        ∀ A : Set (AugmentedIndex n m → ℝ), MeasurableSet A →
          (Q[|{z | z.1 = m ∧ Accepted mu rho H delta n z}])
              {z | augmentedValues n m z.2.2.2.1 ∈ A} =
            (mu[|{v | FirstRecord rho H delta n m v}])
              {v | augmentedValues n m v ∈ A} := by sorry

end FBMStrongSim.RecordBreak.Supplement
