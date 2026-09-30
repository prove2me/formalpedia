-- Prove2me | Theorems.Thm_ComputationalLearning_weak_strong_equivalence
-- name    : ComputationalLearning.weak_strong_equivalence
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:21:24.943352+00:00
-- url     : https://prove2.me/theorems/426c951c-ff85-4717-9f99-72cc76b6d8ed
-- title:
--   Theorem 4.9: if C is weakly PAC learnable using H then C is strongly PAC learnable using ternary majority trees over H
-- statement:
--   **Theorem 4.9.** Let $C$ be any concept class and $H$ any hypothesis class. Then if $C$ is efficiently weakly PAC learnable using $H$, $C$ is efficiently strongly PAC learnable using a hypothesis class of ternary majority trees with leaves from $H$.
--
--   Formally (sample-complexity sense): if $C$ is weakly learnable using measurable hypotheses in $H$ (some constant advantage $\gamma > 0$, confidence $\delta_0 > 0$, sample size $m$, by an algorithm jointly measurable in the sample and the instance, uniformly over measurable targets in $C$ and all distributions), then $C$ is PAC learnable using the class of ternary majority trees with leaves from $H$: for all $0 < \epsilon, \delta < 1/2$ there are a sample size and a learning algorithm outputting majority trees over $H$ with error greater than $\epsilon$ with probability at most $\delta$, for every measurable target in $C$ and every distribution. The algorithm is Strong-Learn of §4.3.3 (recursive modest boosting on filtered distributions sampled by rejection from the sample) with the confidence boosting of §4.2; its polynomial running time is not formalized.
--
--   **Why the learner is measurable.** Strong-Learn runs $L$ on distributions filtered through $L$'s own earlier hypotheses, so its analysis conditions on the earlier samples and integrates. For an arbitrary function $L$ that integral need not exist. Outer-measure bounds on the separate runs do not combine: there are sets, under the continuum hypothesis, whose sections all have measure $0$ while the whole has full outer measure. The book's weak learner is an algorithm, and every algorithm is measurable.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §4.3 pp. 78-100, Theorem 4.9 (Schapire) with the recursive accuracy boosting algorithm Strong-Learn and Lemmas 4.2-4.8

import Definitions.Def_ComputationalLearning_Boosting

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

/-- **Theorem 4.9** (p. 100). Let `C` be any concept class and `H` any hypothesis class. Then if
`C` is efficiently weakly PAC learnable using `H`, `C` is efficiently strongly PAC learnable using
a hypothesis class of ternary majority trees with leaves from `H`. Stated in the
sample-complexity sense: if for some constant advantage `γ > 0`, confidence `δ₀ > 0` and sample
size a jointly measurable algorithm outputs hypotheses in `H` with error at most `1/2 − γ` with probability at
least `δ₀`, for every measurable target in `C` and every distribution, then `C` is PAC learnable
using the class of ternary majority trees over `H` (the recursive accuracy boosting of §4.3
with the confidence boosting of §4.2; running time is not modelled). -/
theorem weak_strong_equivalence {X : Type*} [MeasurableSpace X] (C H : Set (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) (hweak : WeaklyLearnable C H) :
    PACLearnable C (majorityTrees H) := by sorry

end ComputationalLearning
