-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoffInverse_is_threshold
-- name    : BanditAlgorithm.chernoffInverse_is_threshold
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:31:07.108726+00:00
-- url     : https://prove2.me/theorems/a17a4492-f94a-466b-8c44-dc88f15b2fc3
-- title:
--   The Chernoff inverse is a genuine threshold
-- statement:
--   The threshold constant $f^{-1}(\delta)$ of Lattimore--Szepesv\'ari Lemma 33.7, defined as $\inf\{x\ge k:f(x)\le\delta\}$ for $f(x)=e^{k-x}(x/k)^k$, is a genuine inverse: for $k\ge1$ and $\delta>0$ it satisfies $f^{-1}(\delta)\ge k$, $f\bigl(f^{-1}(\delta)\bigr)\le\delta$, and $f(x)\le\delta$ for every $x\ge f^{-1}(\delta)$.
--
--   The last clause is the one the analysis uses -- the threshold works at every round, not just at the critical value. The content is that $f$ is continuous and strictly decreasing on $[k,\infty)$ with $f(k)=1$ and $f(x)\to0$, so the defining set is a nonempty closed up-set and its infimum is attained. Defining $f^{-1}$ by an infimum rather than by inverting $f$ avoids having to produce a global inverse function.
-- source:
--   Elementary property of f(x) = e^{k-x}(x/k)^k and its inverse, the functions introduced in Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 410. The lemma uses f^{-1} without constructing it; this supplies the construction.

import Definitions.Def_TrackAndStop

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

theorem BanditAlgorithm.chernoffInverse_is_threshold {k : ℕ} (hk : 0 < k) {δ : ℝ}
    (hδ : 0 < δ) :
    (k : ℝ) ≤ BanditAlgorithm.chernoffInverse k δ ∧
      BanditAlgorithm.chernoffF k (BanditAlgorithm.chernoffInverse k δ) ≤ δ ∧
      ∀ x : ℝ, BanditAlgorithm.chernoffInverse k δ ≤ x →
        BanditAlgorithm.chernoffF k x ≤ δ := by
  sorry
