-- Prove2me | Theorems.Thm_DynSort_Supplement_theorem_39
-- name    : DynSort.Supplement.theorem_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:42:11.720313+00:00
-- url     : https://prove2.me/theorems/2a335b08-d937-497e-aa85-6497b7fb9990
-- title:
--   Theorem 39 — insertion-only tradeoffs $O(R\log^{1/R}n)$ with $O(R)$ recourse and $O(C)$ with $O(C\log^{1/C}n)$ recourse
-- statement:
--   Consider the online (insertion-only) sorting problem on $n$ cells with recourse, under the assumption of the Remark after Theorem 39: the optimal cost $\Omega=\max_j x_j-\min_j x_j$ of the complete insertion sequence is known in advance.
--
--   For all constants $c_0,c_1>0$ there are constants $K$ and $N_0$ such that for every $n\ge N_0$:
--
--   1. for every real $R\in[c_0,\,c_1\log\log n]$ and every $\Omega$ there is a deterministic online algorithm on $n$ cells such that, on every sequence $\tau$ of at most $n$ insertions whose values have $\mathrm{OPT}=\Omega$, after every prefix the arrangement is legal with
--   $$\mathrm{cost}(S)\le K\,R\,(\log n)^{1/R}\,\Omega,$$
--   and the total recourse over $\tau$ is at most $K R\,|\tau|$;
--   2. for every real $C\in[c_0,\,c_1\log\log n]$ and every $\Omega$ there is a deterministic online algorithm on $n$ cells such that, on every such $\tau$, after every prefix the arrangement is legal with $\mathrm{cost}(S)\le K\,C\,\Omega$, and the total recourse over $\tau$ is at most
--   $$K\,C\,(\log n)^{1/C}\,|\tau|.$$
--
--   Taking $R=1$ gives an $O(\log n)$ ratio with $O(1)$ amortized recourse, $R$ or $C$ of order $\log\log n$ gives Theorem 3, and $C=1$ gives an $O(1)$ ratio with $O(\log n)$ amortized recourse.
--
--   Differences from the source:
--   - reading: R ∈ [O(1), O(log log n)] (resp. C ∈ [O(1), O(log log n)]) → ∀ c₀ > 0, ∀ c₁ > 0, ∃ K N₀, ∀ n ≥ N₀, ∀ R ∈ [c₀, c₁·log log n] (resp. C); reason: the strongest reading: the hidden constants may depend on the constants delimiting the range; the paper's own corollaries (p.34: R = O(1) for an O(log n) ratio, C = O(1) for an O(1) ratio) need every fixed constant to be admissible, which the reading with existential c₀, c₁ would not give
--   - reading: 'with recourse R' and 'competitive ratio of C' → total recourse ≤ K·R·|τ| and cost ≤ K·C·Ω, one K for both clauses; reason: the proof (p.38) states 'with O(R) amortized recourse' and 'with O(C) competitiveness'
--   - encoding: the optimal cost of the complete insertion sequence is known to the algorithm (Remark, p.34) → ∀ Ω before ∃ alg; the guarantee covers every insertion-only τ with opt (insertedValues τ) = Ω; reason: an algorithm chosen after a parameter given in advance is an algorithm that knows that parameter; the sequences with complete optimum Ω are exactly those on which the assumption holds
--   - reading: competitive ratio ρ in online sorting with known optimum → after every prefix of τ the arrangement is legal and its cost is at most ρ·Ω; reason: the paper bounds the cost at any intermediate stage (Claims 40, 41, Lemmas 42, 43) against the known final optimum; this is the guarantee Theorem 4 needs from an online algorithm
--   - encoding: deterministic online algorithm on an array of size n; amortized recourse → the published DynSort.OnlineAlg n (a function of the update history), totalRecourse alg τ ≤ bound·|τ|; reason: the published model of the base mission (§2 definitions); amortized recourse is total recourse divided by the number of updates
--   - encoding: log^{1/R} n, log log n → Real.log n ^ (1 / R), Real.log (Real.log n); N₀ threshold; reason: log is Real.log; the exponent 1/R is kept exactly; N₀ is needed because log log n ≤ 0 for n ≤ 2
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), Theorem 39, §7, p.34 (PDF p.36); assumption: Remark after Theorem 39, p.34 (PDF p.36); O(R), O(C) readings: proof of Theorem 39, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_DynSort_cost
import Definitions.Def_DynSort_OnlineAlg
import Definitions.Def_DynSort_Supplement_InsertOnly

namespace DynSort.Supplement

open DynSort

/-- **Theorem 39**, Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §7, p.34 (PDF p.36): "There are deterministic algorithms for the online
sorting problem that achieve the following tradeoffs: competitive ratio of O(R · log^{1/R} n) with
recourse R ∈ [O(1), O(log log n)], and competitive ratio of C ∈ [O(1), O(log log n)] with
recourse O(C · log^{1/C} n)." Under the Remark on p.34: "the optimal cost of the complete
insertion sequence is known to the algorithm."

**Formalization Note.** The range `[O(1), O(log log n)]` is read as: for every pair of constants
`c₀, c₁ > 0` there are `K` and `N₀` (depending only on `c₀, c₁`) such that for every `n ≥ N₀`
and every real parameter `R` (resp. `C`) in `[c₀, c₁·log log n]` the tradeoff holds. "Recourse
R" and "competitive ratio of C" are `O(R)` and `O(C)` (the proof, p.38: "with O(R) amortized
recourse", "with O(C) competitiveness"). One `K` serves both clauses. The known optimum is a real
`Ω` given in advance; the guarantee covers every insertion-only sequence `τ` of at most `n`
insertions with `opt (insertedValues τ) = Ω`: after every prefix of `τ` the arrangement is legal
with cost at most the stated multiple of `Ω`, and the total recourse over `τ` is at most the
stated multiple of `|τ|`. `log` is `Real.log`; `log^{1/R} n` is `Real.log n ^ (1 / R)`. -/
theorem theorem_39 :
    ∀ c₀ : ℝ, 0 < c₀ → ∀ c₁ : ℝ, 0 < c₁ → ∃ K : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (∀ R : ℝ, c₀ ≤ R → R ≤ c₁ * Real.log (Real.log n) → ∀ Ω : ℝ, ∃ alg : OnlineAlg n,
        ∀ τ : List Update, InsertOnly τ → Valid n τ → opt (insertedValues τ) = Ω →
          (∀ k ≤ τ.length, Legal n (τ.take k) (alg (τ.take k)) ∧
            cost (seq (τ.take k) (alg (τ.take k))) ≤ K * R * Real.log n ^ (1 / R) * Ω) ∧
          (totalRecourse alg τ : ℝ) ≤ K * R * τ.length) ∧
      (∀ C : ℝ, c₀ ≤ C → C ≤ c₁ * Real.log (Real.log n) → ∀ Ω : ℝ, ∃ alg : OnlineAlg n,
        ∀ τ : List Update, InsertOnly τ → Valid n τ → opt (insertedValues τ) = Ω →
          (∀ k ≤ τ.length, Legal n (τ.take k) (alg (τ.take k)) ∧
            cost (seq (τ.take k) (alg (τ.take k))) ≤ K * C * Ω) ∧
          (totalRecourse alg τ : ℝ) ≤ K * C * Real.log n ^ (1 / C) * τ.length) := by sorry

end DynSort.Supplement
