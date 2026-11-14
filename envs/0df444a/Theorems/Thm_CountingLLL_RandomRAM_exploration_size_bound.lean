-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_exploration_size_bound
-- name    : CountingLLL.RandomRAM.exploration_size_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:06:25.695195+00:00
-- url     : https://prove2.me/theorems/d395a343-fc91-4109-8630-42a6e5bfaf69
-- title:
--   Expected size of adaptive tree exploration
-- statement:
--   Consider a finite family of possible adaptive tests. For test j let A_j be the event that it is performed and B_j the event that it accepts. Suppose Pr(B_j)<=p Pr(A_j) for every j, the root is accepted with probability at most p_0, and pointwise the number of tests is at most D^2 times the accepted-tree size, where tree size is the root indicator plus the number of accepted tests. If p>=0 and pD^2<1, the expected tree size is at most p_0/(1-pD^2). The per-test event inequalities are explicit hypotheses: applying this to Algorithm 2 still requires establishing them from its transcript-conditioned sampling rule.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 5.7, equation (32), Section 5.2.3, PDF p.20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory
open scoped BigOperators

theorem CountingLLL.RandomRAM.exploration_size_bound {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (root : Set Ω) (tested accepted : ι → Set Ω) (p p0 D : ℝ)
    (hroot : MeasurableSet root) (htested : ∀ j, MeasurableSet (tested j))
    (haccepted : ∀ j, MeasurableSet (accepted j))
    (hp : 0 ≤ p) (hsub : p * D^2 < 1)
    (hrootprob : μ.real root ≤ p0)
    (hlocal : ∀ j, μ.real (accepted j) ≤ p * μ.real (tested j))
    (hsteps : ∀ ω,
      (∑ j, (tested j).indicator (1 : Ω → ℝ) ω) ≤ D^2 *
      (root.indicator (1 : Ω → ℝ) ω + ∑ j, (accepted j).indicator (1 : Ω → ℝ) ω)) :
    (∫ ω, root.indicator (1 : Ω → ℝ) ω +
      ∑ j, (accepted j).indicator (1 : Ω → ℝ) ω ∂μ) ≤ p0 / (1-p*D^2) := by sorry
