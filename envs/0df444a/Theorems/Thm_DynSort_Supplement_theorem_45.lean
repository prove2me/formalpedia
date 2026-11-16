-- Prove2me | Theorems.Thm_DynSort_Supplement_theorem_45
-- name    : DynSort.Supplement.theorem_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:42:53.183149+00:00
-- url     : https://prove2.me/theorems/d1a54504-6882-4411-b27e-f46b380afd4c
-- title:
--   Theorem 45 — fully dynamic tradeoffs with $(1+\varepsilon)n$ cells
-- statement:
--   Fully dynamic sorting with extra space: at most $n$ real-valued elements are stored in an array of $\lfloor(1+\varepsilon)n\rfloor$ cells under insertions and deletions, and, as in Section 8, the minimum and the maximum value are two permanent elements, never deleted. The cost of the stored values $S$ read left to right is compared with $\mathrm{OPT}(S)=\max S-\min S$.
--
--   For all constants $c_0,c_1>0$ there are constants $K$ and $N_0$ such that for every $\varepsilon>0$ and every $n\ge N_0$:
--
--   1. for every real $R\in[c_0,\,c_1\log\log n]$ there is a deterministic online algorithm on $\lfloor(1+\varepsilon)n\rfloor$ cells such that on every valid update sequence $\sigma$ with two permanent extreme elements, after every update the arrangement is legal with
--   $$\mathrm{cost}(S)\le K\,R\,(\log n)^{1/R}\,\mathrm{OPT}(S),$$
--   and the total recourse over $\sigma$ is at most $(KR+K/\varepsilon)\,|\sigma|$;
--   2. for every real $C\in[c_0,\,c_1\log\log n]$ there is such an algorithm with $\mathrm{cost}(S)\le K\,C\,\mathrm{OPT}(S)$ after every update and total recourse at most
--   $$K\Big(C\,(\log n)^{1/C}+\frac1\varepsilon\Big)|\sigma|.$$
--
--   So the insertion-only tradeoffs of Theorem 39 carry over to the fully dynamic setting when the array has a constant fraction of extra space, without the known-optimum assumption.
--
--   Differences from the source:
--   - reading: R ∈ [O(1), O(log log n)] (resp. C ∈ [O(1), O(log log n)]) → ∀ c₀ > 0, ∀ c₁ > 0, ∃ K N₀, ∀ n ≥ N₀, ∀ R ∈ [c₀, c₁·log log n] (resp. C); reason: the strongest reading: the hidden constants may depend on the constants delimiting the range; the paper's own corollaries (p.34: R = O(1) for an O(log n) ratio, C = O(1) for an O(1) ratio) need every fixed constant to be admissible, which the reading with existential c₀, c₁ would not give
--   - reading: For any ε > 0, ... recourse R + O(1/ε) (resp. O(C·log^{1/C} n + 1/ε)) → K and N₀ chosen before ε; total recourse ≤ (K·R + K/ε)·|σ| (resp. K·(C·log^{1/C} n + 1/ε)·|σ|); reason: O(1/ε) is uniform in ε; the stronger placement of N₀ before ε also holds, since the reduction of Theorem 4 is uniform in ε and the insertion-only algorithms it is applied to do not depend on ε; 'recourse R' is O(R) as in Theorem 39 (p.38)
--   - reading: competitive ratio O(R·log^{1/R} n) (resp. C) for dynamic sorting → cost ≤ K·R·log^{1/R} n·OPT (resp. K·C·OPT) of the stored elements, for every valid σ; reason: the fully dynamic notion of §2, bounded after every update
--   - encoding: the minimum and maximum values are two permanent elements that cannot be deleted (Remark, p.38; in particular values in [0, 1] with 0 and 1 present) → PermanentExtremes σ: for some lo ≤ hi the first two updates insert lo and hi (either order), every inserted value lies in [lo, hi], elements 0 and 1 are never deleted; reason: elements present throughout the execution are the first two inserted; [0, 1] is the case lo = 0, hi = 1, and rescaling values changes neither cost ratios nor recourse
--   - reading: an array of size (1 + ε)n → OnlineAlg ⌊(1 + ε)·n⌋₊ with Valid n (at most n elements present); reason: the array size must be an integer; the floor is the smaller array, so the stronger reading
--   - encoding: deterministic online algorithm on an array of size n; amortized recourse → the published DynSort.OnlineAlg n (a function of the update history), totalRecourse alg τ ≤ bound·|τ|; reason: the published model of the base mission (§2 definitions); amortized recourse is total recourse divided by the number of updates
--   - encoding: log^{1/R} n, log log n → Real.log n ^ (1 / R), Real.log (Real.log n); N₀ threshold; reason: log is Real.log; the exponent 1/R is kept exactly; N₀ is needed because log log n ≤ 0 for n ≤ 2
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Theorem 45, §8, p.39 (PDF p.41); assumption: Remark after Claim 44, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_DynSort_cost
import Definitions.Def_DynSort_OnlineAlg
import Definitions.Def_DynSort_Supplement_PermanentExtremes

namespace DynSort.Supplement

open DynSort

/-- **Theorem 45**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §8, p.39 (PDF p.41): "For any ε > 0, there are deterministic algorithms for
dynamic sorting that maintain at most n elements in an array of size (1 + ε)n with the following
tradeoffs: competitive ratio of O(R · log^{1/R} n) with recourse R + O(1/ε), where
R ∈ [O(1), O(log log n)], and competitive ratio of C ∈ [O(1), O(log log n)] with recourse
O(C · log^{1/C} n + 1/ε)." Under the Remark on p.38: the minimum and maximum values are two
permanent elements.

**Formalization Note.** For every pair of constants `c₀, c₁ > 0` there are `K` and `N₀`
(depending only on `c₀, c₁`, not on `ε`) such that for every `ε > 0`, every `n ≥ N₀` and every
real `R` (resp. `C`) in `[c₀, c₁·log log n]` there is an online algorithm on `⌊(1+ε)·n⌋` cells
that, on every valid update sequence with at most `n` elements present and two permanent extreme
elements, is legal, has cost at most `K·R·log^{1/R} n·opt` (resp. `K·C·opt`) after every update
and total recourse at most `(K·R + K/ε)·|σ|` (resp. `K·(C·log^{1/C} n + 1/ε)·|σ|`). "Recourse
R + O(1/ε)" is `O(R) + O(1/ε)` (Theorem 39's recourse `R` is `O(R)`, p.38). `opt` is that of
the stored elements, the fully dynamic notion. `log` is `Real.log`. -/
theorem theorem_45 :
    ∀ c₀ : ℝ, 0 < c₀ → ∀ c₁ : ℝ, 0 < c₁ → ∃ K : ℝ, ∃ N₀ : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ n : ℕ, N₀ ≤ n →
      (∀ R : ℝ, c₀ ≤ R → R ≤ c₁ * Real.log (Real.log n) →
        ∃ alg : OnlineAlg ⌊(1 + ε) * n⌋₊, ∀ σ : List Update, Valid n σ → PermanentExtremes σ →
          Legal ⌊(1 + ε) * n⌋₊ σ (alg σ) ∧
          cost (seq σ (alg σ)) ≤ K * R * Real.log n ^ (1 / R) * opt (seq σ (alg σ)) ∧
          (totalRecourse alg σ : ℝ) ≤ (K * R + K / ε) * σ.length) ∧
      (∀ C : ℝ, c₀ ≤ C → C ≤ c₁ * Real.log (Real.log n) →
        ∃ alg : OnlineAlg ⌊(1 + ε) * n⌋₊, ∀ σ : List Update, Valid n σ → PermanentExtremes σ →
          Legal ⌊(1 + ε) * n⌋₊ σ (alg σ) ∧
          cost (seq σ (alg σ)) ≤ K * C * opt (seq σ (alg σ)) ∧
          (totalRecourse alg σ : ℝ) ≤ K * (C * Real.log n ^ (1 / C) + 1 / ε) * σ.length) := by sorry

end DynSort.Supplement
