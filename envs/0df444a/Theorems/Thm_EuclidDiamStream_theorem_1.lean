-- Prove2me | Theorems.Thm_EuclidDiamStream_theorem_1
-- name    : EuclidDiamStream.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:43.505635+00:00
-- url     : https://prove2.me/theorems/c1beb298-620c-43c1-a778-b185876a2541
-- title:
--   Theorem 1 — streaming algorithms for the $(r,c,n)$-diameter problem need $n^{\tilde\Omega(1/c^2)}\log(m+1)$ bits
-- statement:
--   There are absolute constants $\delta_0,C>0$ and $n_0$ such that the following holds for every $\delta\in(0,\delta_0]$, $c>1$, $n\ge n_0$ and $\Delta\ge1$. Let $d=d(n,c)$ and $r=\sqrt d/(c\sqrt3)$. If $\mathcal A$ is a randomized streaming algorithm with bounded randomness complexity that solves the $(r,c,n)$-diameter problem with error $\delta$ on the grid $\{0,\dots,\Delta\}^d$, then for all $m\in\mathbb N$,
--   $$\mathcal S^+(\mathcal A,m)\ge n^{C/(c^2\log_2(2c))}\cdot\log_2(m+1).$$
--
--   This is the main result of the paper. It shows that Indyk's $n^{O(1/c^2)}$-space algorithm for $c$-approximating the Euclidean diameter of $n$ points in a dynamic stream is optimal up to a logarithmic factor in the exponent.
--
--   **Formalization Note** The exact state-counting measure $\mathcal S^+$ lies in $\mathbb N\cup\{\infty\}$, and the inequality is taken in the extended nonnegative reals.
--
--   Differences from the source:
--   - reading: A solves the (r,c,n)-diameter problem for unnamed r, c, d → d = hardDim n c, r = hardScale n c, c > 1; reason: for arbitrary r the statement is false: at r ≥ Δ√d the constant-0 algorithm solves the problem with S⁺ = 0; Lemma 3.9, which the proof uses, fixes these values
--   - reading: S⁺ = n^{Ω̃(1/c²)}·log(m+1) → S⁺ ≥ n^{C/(c²·log₂(2c))}·log₂(m+1) with C absolute; reason: the proof gives n^{Ω(1/(c² log c))} (p.13); log₂(2c) is the form uniform as c → 1⁺, and base 2 is the strongest, because S⁺ counts bits
--   - reading: δ "a sufficiently small constant", n and Δ unnamed → δ₀, C, n₀ absolute and before δ, c, n, Δ, A, m; δ ≤ δ₀, n ≥ n₀, Δ ≥ 1; reason: absolute constants are the strongest order; a small n carries no content in an Ω̃ statement, and Δ ≥ 1 is what lets the hypercube sit in the grid
--   - reading: "any stream" in Def. 2.1 and Def. 2.3 → every strict-turnstile stream (BoolCSPDel.IsLegal), of any length and frequency; reason: footnote 6, p.6: the lower bounds work in the strict turnstile model
--   - reading: diam(v) a maximum over supp(v), which is empty at v = 0 → diam 0 = 0, so A must answer 0 on streams ending empty; reason: the usual diameter of the empty set; D never draws v = 0
--   - encoding: "=" in S⁺ = n^{Ω̃(1/c²)}·log(m+1) → ≤ in ℝ≥0∞; reason: Ω̃ is a lower bound
--   - encoding: bounded randomness complexity; "all settings of randomness" → a Fintype seed type with any PMF, fixed before the stream; W⁺ over seeds in μ.support; reason: pp.3, 13: a finite amount of randomness independent of stream length; a seed of probability zero is never drawn
--   - encoding: S⁺(A,·) : ℕ → ℕ → spaceComplexity in ℕ∞, with ⊤ when W⁺ is infinite; reason: the state type is arbitrary; on a finite W⁺ it equals ⌈log₂|W⁺|⌉, and the bound holds trivially at ⊤
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.2, Theorem 1 (restated p.13)

import Mathlib
import Definitions.Def_EuclidDiamStream_hardDim
import Definitions.Def_EuclidDiamStream_Solves
import Definitions.Def_EuclidDiamStream_spaceComplexity

namespace EuclidDiamStream

/-- Theorem 1 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.2 (restated p.13): any randomized streaming algorithm `A` which solves the `(r,c,n)`-diameter
problem using bounded randomness complexity has `S⁺(A,m) = n^{Ω̃(1/c²)} · log(m+1)` for all `m ∈ ℕ`.

**Formalization Note.** The theorem is about the instance its proof uses (Lemma 3.9): dimension `d = d(n,c)` and
`r = √d/(c√3)` (for arbitrary `r` the statement is false: at `r ≥ Δ√d` the constant-0 algorithm uses no space).
Streams are strict turnstile (footnote 6, p.6), with no bound on length or frequency. `Ω̃` is read as the exponent
`C/(c²·log₂(2c))` with `δ₀, C, n₀` absolute and before `δ, c, n, Δ, A, m`; `log` has base 2. `S⁺` lies in `ℕ∞`, and the
inequality is taken in `ℝ≥0∞`. -/
theorem theorem_1 :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ c : ℝ, 1 < c → ∀ n : ℕ, n₀ ≤ n → ∀ Δ : ℕ, 1 ≤ Δ →
      ∀ (R W : Type) [Fintype R] (A : StreamAlg (Point (hardDim n c) Δ) R W),
        A.Solves (hardScale n c) c n δ →
        ∀ m : ℕ,
          ENNReal.ofReal ((n : ℝ) ^ (C / (c ^ 2 * Real.logb 2 (2 * c))) * Real.logb 2 ((m : ℝ) + 1)) ≤
            ((A.spaceComplexity m : ℕ∞) : ENNReal) := by sorry

end EuclidDiamStream
