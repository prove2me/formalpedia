-- Prove2me | Theorems.Thm_DetStreamClique_MaxClique_lemma_3_10
-- name    : DetStreamClique.MaxClique.lemma_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:58:05.73999+00:00
-- url     : https://prove2.me/theorems/8bf99800-4ae5-42ed-b6bb-3cd7b5e09a68
-- title:
--   Lemma 3.10 — a packing with both Θ bounds
-- statement:
--   There are absolute positive constants $c,C$ and an integer $N\ge2$ such that, for every $n\ge N$ and every real $b$ with $1\le b\le\sqrt n/36$ and $18b$ integral, there are $\ell$ subsets $B_i\subseteq\operatorname{Fin}(n)$ satisfying
--   $$|B_i|=18b,\qquad |B_i\cap B_j|\le1\ (i\ne j),\qquad c n^2/b^2\le\ell\le C n^2/b^2.$$
--   Both constants and the threshold are uniform in $b$. This is the block packing needed for the multi-gadget distribution.
--
--   Differences from the source:
--   - encoding: |B_i|=18b → the hypothesis 18b is integral; subsets of Fin n; reason: this is precisely the integrality implicit in the source cardinality
--   - encoding: ℓ=Θ(n²/b²), with n sufficiently large → positive uniform lower and upper constants, with a common threshold before n and b; reason: this makes the two asymptotic inequalities explicit without changing their instances
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, Lemma 3.10, p. 16

import Mathlib

open scoped Classical BigOperators

namespace DetStreamClique.MaxClique

/-- Lemma 3.10, p. 16: both sides of Theta, uniformly in real b. -/
theorem lemma_3_10 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ b : ℝ, 1 ≤ b →
        b ≤ Real.sqrt (n : ℝ) / 36 →
        (∃ r : ℕ, (r : ℝ) = 18 * b) →
        ∃ (ℓ : ℕ) (B : Fin ℓ → Finset (Fin n)),
          (∀ i, ((B i).card : ℝ) = 18 * b) ∧
          (∀ i j, i ≠ j → ((B i) ∩ (B j)).card ≤ 1) ∧
          c * (n : ℝ)^2 / b^2 ≤ (ℓ : ℝ) ∧
          (ℓ : ℝ) ≤ C * (n : ℝ)^2 / b^2 := by sorry

end DetStreamClique.MaxClique
