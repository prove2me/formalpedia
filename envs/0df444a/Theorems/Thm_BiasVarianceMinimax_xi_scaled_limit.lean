-- Prove2me | Theorems.Thm_BiasVarianceMinimax_xi_scaled_limit
-- name    : BiasVarianceMinimax.xi_scaled_limit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:37.853846+00:00
-- url     : https://prove2.me/theorems/94d6755a-6766-4e99-942a-d8133a1ef29f
-- title:
--   (25), (75) — the scaled limit of $\Xi$
-- statement:
--   As $n\to\infty$,
--
--   $$\xi_{11}\to 0,\qquad n^{q_1/(2(q_1+q_2))}\xi_{12}\to 0,\qquad n^{q_1/(2(q_1+q_2))}\xi_{21}\to 0,\qquad n^{q_1/(q_1+q_2)}\xi_{22}\to\frac{q_1}{q_1+q_2}.$$
--
--   Equivalently, with $a=\tilde a/n^{q_1/(2(q_1+q_2))}$, the scaled quadratic form is $[\tilde a\ \ 1](\tilde\Xi+o(1))[\tilde a\ \ 1]^\top$ with $\tilde\Xi=\begin{bmatrix}0&0\\0&q_1/(q_1+q_2)\end{bmatrix}$ and $o(1)$ independent of $\tilde a$, which is (75).
--
--   Differences from the source:
--   - generalization: Appendix C assumes n₀ = 0 → the statement holds for every n₀ ∈ ℕ; reason: specializes to the page at n₀ = 0; Theorem 8 needs n₀
--   - encoding: the matrix identity (75) with a matrix o(1) → four entrywise limits; reason: the o(1) of (75) is independent of ã, so the two forms are the same
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, (25), p.21; (75), p.54

import Mathlib
import Definitions.Def_BiasVarianceMinimax_xi

open Filter Topology

namespace BiasVarianceMinimax

/-- **The scaled limit of `Ξ`.** Lam, Zhang & Zhang, arXiv:1902.04673v1, (25), p.21; (75), p.54:
`n^(q₁/(q₁+q₂)) Z̄ₙ∗(ã)² = [ã 1] (Ξ̃ + o(1)) [ã; 1]` with `Ξ̃ = [0 0; 0 q₁/(q₁+q₂)]`.

**Formalization Note.** Here `Z̄ₙ∗(ã)² = [a 1] Ξ [a; 1]` with `a = ã/n^(q₁/(2(q₁+q₂)))`, so the matrix
of (75) has entries `ξ₁₁`, `n^(q₁/(2(q₁+q₂))) ξ₁₂`, `n^(q₁/(2(q₁+q₂))) ξ₂₁`, `n^(q₁/(q₁+q₂)) ξ₂₂`. The
`o(1)` is a matrix independent of `ã`, stated entrywise. With the shift `n₀`. -/
theorem xi_scaled_limit (q₁ q₂ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (n₀ : ℕ) :
    Tendsto (fun n : ℕ => xi q₁ q₂ n₀ n 0 0) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ (q₁ / (2 * (q₁ + q₂))) * xi q₁ q₂ n₀ n 0 1) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ (q₁ / (2 * (q₁ + q₂))) * xi q₁ q₂ n₀ n 1 0) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ (q₁ / (q₁ + q₂)) * xi q₁ q₂ n₀ n 1 1) atTop
      (𝓝 (q₁ / (q₁ + q₂))) := by sorry

end BiasVarianceMinimax
