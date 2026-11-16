-- Prove2me | Theorems.Thm_DynSort_Supplement_theorem_4
-- name    : DynSort.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:40:32.61395+00:00
-- url     : https://prove2.me/theorems/f9efcfe8-8baa-4aee-93f2-2c06f11b2c7c
-- title:
--   Theorem 4 — with $(1+\varepsilon)n$ cells, online sorting reduces to fully dynamic sorting
-- statement:
--   Fully dynamic sorting maintains at most $n$ real-valued elements in an array under insertions and deletions; its cost is $\mathrm{cost}(S)=\sum_j|x_{j+1}-x_j|$ for the stored values $S=(x_1,\dots,x_k)$ read left to right, compared with $\mathrm{OPT}(S)=\max S-\min S$. As in Section 8, the minimum and the maximum value are two permanent elements, never deleted.
--
--   There is a constant $K$ such that the following holds for every $\varepsilon>0$, every $n$ and all reals $c$ and $r\ge 0$. Let $A$ be a deterministic online sorting algorithm on $\lfloor\varepsilon n\rfloor$ cells which is told a value window $[\ell,h]$ in advance and which, on every sequence of at most $\lfloor\varepsilon n\rfloor$ insertions of values in $[\ell,h]$, keeps a legal arrangement with
--   $$\mathrm{cost}(S)\le c\,(h-\ell)\quad\text{after every insertion},\qquad \text{total recourse}\le r\cdot(\text{number of insertions}).$$
--   (This is the paper's normalization "values in $[0,1]$, cost $c$"; an algorithm with $\mathrm{cost}(S)\le c\cdot\mathrm{OPT}(S)$ after every insertion satisfies it.)
--   Then there is a deterministic fully dynamic sorting algorithm on $\lfloor(1+\varepsilon)n\rfloor$ cells which, on every valid update sequence $\sigma$ with at most $n$ elements present and two permanent extreme elements, keeps a legal arrangement with
--   $$\mathrm{cost}(S)\le (2c+1)\cdot\mathrm{OPT}(S)\quad\text{after every update},\qquad \text{total recourse}\le \Big(r+\frac K\varepsilon\Big)\cdot|\sigma|.$$
--
--   With a constant fraction of extra space, fully dynamic sorting is thus no harder than insertion-only sorting, up to a factor $2$ in the ratio and an additive $O(1/\varepsilon)$ in the recourse.
--
--   Differences from the source:
--   - reading: every deterministic online sorting algorithm with competitive ratio c and amortized recourse r (Claim 44: cost c, values normalized to [0, 1]) → one algorithm A lo hi on ⌊ε·n⌋₊ cells, told the window [lo, hi] in advance, that on every insertion-only sequence of at most ⌊ε·n⌋₊ insertions with values in [lo, hi] is legal, has cost ≤ c·(hi − lo) after every insertion and total recourse ≤ r·|σ|; reason: Claim 44 states the input guarantee in the normalization of the Remark on p.38 (values in [0, 1], cost c, bounded at every intermediate stage, as the proof uses it on the sub-array); this is the weakest hypothesis under which the proof runs, it is implied by cost ≤ c·OPT after every insertion and also admits known-optimum algorithms; the algorithm is assumed only at the sub-array size ⌊εn⌋ the transformation uses, which is weaker than assuming it at every size; so the statement implies every stronger-hypothesis reading
--   - encoding: amortized recourse r (a real number) → hypothesis 0 ≤ r; reason: a recourse bound is nonnegative; the hypothesis on A forces r ≥ 0 when ⌊εn⌋ ≥ 1 (and c ≥ 0 always, c ≥ 1 when ⌊εn⌋ ≥ 2), so 0 ≤ r only excludes a meaningless negative r in the degenerate case ⌊εn⌋ = 0
--   - encoding: the minimum and maximum values are two permanent elements that cannot be deleted (Remark, p.38; in particular values in [0, 1] with 0 and 1 present) → PermanentExtremes σ: for some lo ≤ hi the first two updates insert lo and hi (either order), every inserted value lies in [lo, hi], elements 0 and 1 are never deleted; reason: elements present throughout the execution are the first two inserted; [0, 1] is the case lo = 0, hi = 1, and rescaling values changes neither cost ratios nor recourse
--   - reading: an array of size (1 + ε)n → OnlineAlg ⌊(1 + ε)·n⌋₊ with Valid n (at most n elements present); reason: the array size must be an integer; the floor is the smaller array, so the stronger reading
--   - encoding: competitive ratio 2c + 1 and amortized recourse r + O(1/ε) per update in the fully dynamic setting → ∃ K before ε, n, c, r: for every valid σ with at most n elements present, cost ≤ (2c + 1)·OPT of the stored elements and total recourse ≤ (r + K/ε)·|σ|; reason: O(1/ε) is uniform in ε (otherwise it would read O(1)); the ratio 2c + 1 is exact as printed; σ ranges over all valid sequences, so the bounds hold after every update
--   - encoding: deterministic online algorithm on an array of size n; amortized recourse → the published DynSort.OnlineAlg n (a function of the update history), totalRecourse alg τ ≤ bound·|τ|; reason: the published model of the base mission (§2 definitions); amortized recourse is total recourse divided by the number of updates
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Theorem 4, §1.1, p.2 (PDF p.4); proved as Claim 44, §8, p.38 (PDF p.40); assumption: Remark after Claim 44, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_DynSort_cost
import Definitions.Def_DynSort_OnlineAlg
import Definitions.Def_DynSort_Supplement_InsertOnly
import Definitions.Def_DynSort_Supplement_PermanentExtremes

namespace DynSort.Supplement

open DynSort

/-- **Theorem 4**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §1.1, p.2 (PDF p.4); proved as Claim 44, §8, p.38 (PDF p.40): "Suppose the
array has size (1 + ε)n for any fixed ε > 0. Then every deterministic online sorting algorithm with
competitive ratio c and amortized recourse r can be transformed into a deterministic fully dynamic
sorting algorithm with competitive ratio 2c + 1 and amortized recourse r + O(1/ε) per update."
Under the Remark on p.38: the minimum and maximum values are two permanent elements.

**Formalization Note.** One constant `K` (the `O(1/ε)`), chosen before `ε`, `n`, `c`, `r`.
The input online sorting algorithm runs on `⌊ε·n⌋` cells, the sub-array the reduction of Claim 44
uses. Its guarantee is the one Claim 44 states under the normalization of the Remark on p.38
("all values lie in [0, 1]", "cost c"): the algorithm is told a window `[lo, hi]` in advance
(`A lo hi`), and on every insertion-only sequence of at most `⌊ε·n⌋` insertions whose values lie
in `[lo, hi]` it is legal, has cost at most `c·(hi − lo)` after every insertion and total recourse
at most `r·|σ|`. This hypothesis is implied by the stronger `cost ≤ c·opt` after every insertion
(take `A lo hi` independent of the window), and it also admits algorithms that use a known bound on
the optimum. `r ≥ 0` (a recourse bound; it only matters when `⌊ε·n⌋ = 0`). The output algorithm runs
on `⌊(1+ε)·n⌋` cells and, on every valid update sequence with at most `n` elements present and two
permanent extreme elements (`PermanentExtremes`), is legal, has cost at most `(2c+1)·opt` after
every update, and total recourse at most `(r + K/ε)·|σ|`. -/
theorem theorem_4 :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ c r : ℝ, 0 ≤ r →
      ∀ A : ℝ → ℝ → OnlineAlg ⌊ε * n⌋₊,
        (∀ lo hi : ℝ, lo ≤ hi → ∀ σ : List Update, InsertOnly σ → Valid ⌊ε * n⌋₊ σ →
          (∀ x ∈ insertedValues σ, lo ≤ x ∧ x ≤ hi) →
          Legal ⌊ε * n⌋₊ σ (A lo hi σ) ∧
          cost (seq σ (A lo hi σ)) ≤ c * (hi - lo) ∧
          (totalRecourse (A lo hi) σ : ℝ) ≤ r * σ.length) →
        ∃ alg : OnlineAlg ⌊(1 + ε) * n⌋₊, ∀ σ : List Update, Valid n σ → PermanentExtremes σ →
          Legal ⌊(1 + ε) * n⌋₊ σ (alg σ) ∧
          cost (seq σ (alg σ)) ≤ (2 * c + 1) * opt (seq σ (alg σ)) ∧
          (totalRecourse alg σ : ℝ) ≤ (r + K / ε) * σ.length := by sorry

end DynSort.Supplement
