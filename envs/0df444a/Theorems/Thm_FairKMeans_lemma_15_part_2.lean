-- Prove2me | Theorems.Thm_FairKMeans_lemma_15_part_2
-- name    : FairKMeans.lemma_15_part_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:08.895171+00:00
-- url     : https://prove2.me/theorems/b8eda4b0-0a23-4dbb-b80c-78078b600ac9
-- title:
--   Lemma 15, part 2 — means of all $\lceil 1/\delta\rceil$-multisets are a candidate set for weighted centroids (corrected: $n\ge 1$)
-- statement:
--   Let $\delta\in(0,1]$, let $r=\lceil 1/\delta\rceil$, and let $Q=(q_1,\dots,q_n)$ be an indexed set of $n\ge 1$ points of $\mathbb R^d$. Let $W$ be the family of the means $\frac1r\sum_{\ell=1}^r q_{f(\ell)}$ of all multisets of $r$ points of $Q$. Then:
--
--   1. $W$ is a candidate set for weighted centroids of $Q$ with accuracy $\delta$: for all weights $\mu\ge 0$ some $t\in W$ satisfies $\sum_q\mu(q)\|q-t\|^2\le(1+\delta)\min_{c}\sum_q\mu(q)\|q-c\|^2$;
--   2. $W$ has at most $n^r$ distinct points and contains the mean of every $r$-multiset;
--   3. building $W$ is charged at most $n^r\cdot r\cdot d$ arithmetic operations.
--
--   This is the candidate-set construction that makes Algorithm 1 polynomial in every dimension.
--
--   **Formalization Note** The time bound "$O(n^r r d)$" is the operation charge of the mission's cost model (footnote 1).
--
--   Differences from the source:
--   - correction: Q any finite indexed set with n points → n ≥ 1; reason: for n = 0 the set of means is empty, but (17) asks for a point t ∈ W even for the empty weight vector; counterexample: Q empty, any δ
--   - encoding: the set of means of all r-multisets of Q → the family indexed by the n^r ordered r-tuples; size as the number of distinct points; reason: every multiset is the image of a tuple, so the same points
--   - encoding: computed in O(n^r r d) time → operation charge wcsCharge = n^r · r · d; reason: footnote 1 cost model: real-RAM operations counted explicitly
--   - encoding: min over c ∈ ℝ^d → real infimum ⨅ c; reason: the minimum is attained at the μ-weighted centroid (p.20)
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 15, part 2, p.20 (PDF p.22); proof in Appendix A, pp.49–50 (PDF pp.51–52)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_CandidateSets

namespace FairKMeans

/-- **Lemma 15, part 2** (arbitrary dimension), p.20 (PDF 22); proof in Appendix A, pp.49–50
(PDF 51–52). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…).

Let `δ ∈ (0,1]`, `r = ⌈1/δ⌉`, and let `Q` be an indexed set of `q ≥ 1` points. The family of the
means of all multisets of `r` points of `Q` satisfies (17), it has at most `q^r` distinct points,
and its construction is charged at most `q^r · r · d` operations.

**Formalization Note.** `q ≥ 1` is a correction: for `q = 0` the set of means is empty and (17)
fails for the (empty) weight vector, since (17) asks for a point of `W`. The time clause is the
operation charge `wcsCharge` of the mission's cost model. -/
theorem lemma_15_part_2 (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) {d q : ℕ} (Q : Fin q → E d)
    (hq : 0 < q) :
    IsWCS δ Q (wcs δ Q) ∧
      (Finset.univ.image (wcs δ Q)).card ≤ q ^ wcsR δ ∧
      (∀ f : Fin (wcsR δ) → Fin q, ∃ i, wcs δ Q i = multisetMeans (wcsR δ) Q f) ∧
      wcsCharge q δ d ≤ q ^ wcsR δ * wcsR δ * d := by sorry

end FairKMeans
