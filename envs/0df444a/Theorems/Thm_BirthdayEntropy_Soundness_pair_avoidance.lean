-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_pair_avoidance
-- name    : BirthdayEntropy.Soundness.pair_avoidance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:49:46.732201+00:00
-- url     : https://prove2.me/theorems/8503e60c-bce9-4b86-9847-fffdb33b1ee2
-- title:
--   Lemma 4.1 — Pair avoidance under fixed-size sampling
-- statement:
--   Let $U$ be a finite ground set of size $m$ and $P$ a nonempty set of distinct unordered two-element subsets of $U$. Suppose every point is incident to at most $q$ pairs. For $2\le\ell\le m$, a uniform $\ell$-subset $S$ satisfies
--   $$\Pr[\forall e\in P,\ e\nsubseteq S]\le\exp\!\left(-\frac{|P|\ell^2}{4qm^2}\right).$$
--   Nonemptiness and the two-element condition imply $q\ge1$, even though the bound parameter is real. The avoidance probability is the exact ratio of finite counts. This is the pair-avoidance ingredient for the fixed-flattening estimate.
--
--   Differences from the source:
--   - encoding: uniform fixed-size sampling and unordered pairs → finite-set count ratio and a set of two-element finite subsets; reason: the sample space has nonzero binomial cardinality under 2<=ell<=m; no pairs are counted with multiplicity
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma 4.1, PDF pp6 / printed pp5

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Counting

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Lemma 4.1, PDF p6 / printed p5. Distinct unordered pairs; q is real. -/
theorem pair_avoidance {U : Type*} [Fintype U] (P : Finset (Finset U))
    (hP : P.Nonempty) (hpairs : ∀ e ∈ P, e.card = 2)
    (q : ℝ) (hq : ∀ u : U, ((P.filter (fun e => u ∈ e)).card : ℝ) ≤ q)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hℓm : ℓ ≤ Fintype.card U) :
    avoidanceProbability P ℓ ≤ Real.exp
      (-((P.card : ℝ) * (ℓ : ℝ)^2 / (4 * q * (Fintype.card U : ℝ)^2))) := by sorry

end BirthdayEntropy.Soundness
