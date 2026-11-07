-- Prove2me | Theorems.Thm_DynStrings_lemma_5_11_dyadic_sum
-- name    : DynStrings.lemma_5_11_dyadic_sum
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:56:06.455332+00:00
-- url     : https://prove2.me/theorems/7501f22d-abfd-4565-bd04-34f3438f6caa
-- title:
--   Lemma 5.11 — $\Lambda(S\mid\emptyset)=\log n+\sum_{p\ge0}d_{2^p}(S)/2^p+O(1)=O(D)$
-- statement:
--   There is an absolute constant $C_0$ such that for every string $S$ of length $n\ge2$ with $\sigma\ge2$ distinct characters,
--
--   $$\Big|\Lambda(S\mid\emptyset)-\log n-\sum_{p\ge0}\frac{d_{2^p}(S)}{2^p}\Big|\le C_0\qquad\text{and}\qquad \Lambda(S\mid\emptyset)\le C_0\,D .$$
--
--   The dyadic novelty of a single string is within a constant factor of the optimal worst-case space $D=\delta\lg\big(n\log\sigma/(\delta\log n)\big)$, which converts the relative theorem into the static bound.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: O(·) with absolute constants → an explicit constant quantified before the alphabet, the strings and the orders; reason: the paper's convention (p.13) that hidden constants are absolute
--   - encoding: ∑_{p≥0} d_{2^p}(S)/2^p → the sum over 0 ≤ p ≤ n; reason: the terms vanish for 2^p > n, and 2^p > n for every p > n
--   - encoding: = … + O(1) → the absolute difference is at most C₀; reason: O(1) denotes a quantity bounded in absolute value by an absolute constant
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Lemma 5.11, p.26

import Mathlib
import Definitions.Def_DynStrings_Novelty

namespace DynStrings

/-- **Lemma 5.11**, p.26.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

There is an absolute constant `C₀` such that for every string `S` of length `n ≥ 2` with `σ ≥ 2`,
`Λ(S | ∅) = log n + ∑_{p ≥ 0} d_{2^p}(S)/2^p + O(1)` (the error is at most `C₀` in absolute value)
and `Λ(S | ∅) ≤ C₀ D`.

**Formalization Note.** The series `∑_{p ≥ 0}` is summed over `p ≤ n`: its terms vanish for
`2^p > n`. -/
theorem lemma_5_11_dyadic_sum :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (α : Type) [DecidableEq α] (S : List α), 2 ≤ S.length → 2 ≤ sigma S →
      |Lam S 0 - Real.logb 2 S.length -
          ∑ p ∈ Finset.range (S.length + 1), (dsub (2 ^ p) S : ℝ) / 2 ^ p| ≤ C₀ ∧
      Lam S 0 ≤ C₀ * Dspace S := by sorry

end DynStrings
