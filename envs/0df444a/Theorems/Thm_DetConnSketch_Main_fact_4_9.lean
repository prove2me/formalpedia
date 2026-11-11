-- Prove2me | Theorems.Thm_DetConnSketch_Main_fact_4_9
-- name    : DetConnSketch.Main.fact_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:10.89519+00:00
-- url     : https://prove2.me/theorems/cd513160-290a-4f57-b959-f9456a70d6d2
-- title:
--   Fact 4.9 — kernels of random sign matrices: $\|v\|_2\le C_0\sqrt{\log(2n)/D}\,\|v\|_1$ with probability $\ge1-e^{-c_0D}$
-- statement:
--   There are absolute constants $C_0, c_0 > 0$ such that for all $D, n \ge 1$ a random sign matrix $A \in \{-1,1\}^{D\times n}$ with independent uniformly random entries satisfies, with probability at least $1 - e^{-c_0 D}$,
--   $$\|v\|_2 \le C_0 \sqrt{\frac{\log(2n)}{D}}\ \|v\|_1 \qquad\text{for every } v \in \mathbb R^n \text{ with } Av = 0 .$$
--   Here $\|v\|_2 = (\sum_j v_j^2)^{1/2}$, $\|v\|_1 = \sum_j |v_j|$ and $\log$ is the natural logarithm.
--
--   The paper cites it from Mendelson, Pajor and Tomczak-Jaegermann (Corollary 2.5 of [MPTJ05], translated in Appendix B); it gives the null-space property behind Lemma 4.5. It is posed here as stated.
--
--   Differences from the source:
--   - encoding: probability over a uniform random sign matrix → number of A : Fin D → Fin n → Bool (entry sgn (A i j)) satisfying the event ≥ (1 − e^{−c₀D}) · 2^{Dn}; reason: uniform measure on the 2^{Dn} sign matrices
--   - encoding: D × n matrix (D, n implicit positive) → 1 ≤ D and 1 ≤ n; reason: log(2n) and division by D need them; excludes only undefined cases
--   - encoding: ∥v∥₂, ∥v∥₁, ker A → Real.sqrt (∑ v_j²), ∑ |v_j|, real v with ∑_j sgn(A i j) v_j = 0 for every i; reason: same quantities
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 29 (PDF 33), Fact 4.9; p. 98 (PDF 102), Appendix B

import Mathlib
import Definitions.Def_DetConnSketch_Main_Signs

namespace DetConnSketch.Main

/-- Fact 4.9: there are absolute constants `C₀, c₀ > 0` such that for all `D, n ≥ 1` a uniformly
random sign matrix `A ∈ {−1, 1}^{D×n}` satisfies, with probability at least `1 − e^{−c₀ D}`,
`‖v‖₂ ≤ C₀ √(log(2n)/D) ‖v‖₁` for every real `v ∈ ker A`. The probability is counting over the
`2^{Dn}` sign matrices (encoded as `Fin D → Fin n → Bool` through `sgn`). -/
theorem fact_4_9 :
    ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧ ∀ D n : ℕ, 1 ≤ D → 1 ≤ n →
      (1 - Real.exp (-(c₀ * D))) * (2 : ℝ) ^ (D * n) ≤
        (Nat.card {A : Fin D → Fin n → Bool //
          ∀ v : Fin n → ℝ, (∀ i, ∑ j, sgn (A i j) * v j = 0) →
            Real.sqrt (∑ j, v j ^ 2) ≤
              C₀ * Real.sqrt (Real.log (2 * (n : ℝ)) / D) * ∑ j, |v j|} : ℝ) := by sorry

end DetConnSketch.Main
