-- Prove2me | Theorems.Thm_FastFashion_Approx_tangent_slopes_pos_decreasing
-- name    : FastFashion.Approx.tangent_slopes_pos_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:30.087499+00:00
-- url     : https://prove2.me/theorems/079a8e91-c05f-4182-8b7b-a192d36615bf
-- title:
--   §3.1.3, p. 12 — the terms of (4)–(5) are positive and decreasing
-- statement:
--   Let $\lambda > 0$ and $T > 0$, and let $a_k(\lambda) = \gamma(k+1, \lambda T)/(\lambda\, k!)$, $k \in \mathbb N$, be the $(k+1)$-th term of the sum (5). Then for every $k \in \mathbb N$,
--   $$0 < a_k(\lambda) \qquad\text{and}\qquad a_{k+1}(\lambda) < a_k(\lambda).$$
--
--   This is the paper's reason why $\mathbb E[\tau_s \wedge T]$ is a discretely concave function of $q_s$: it is a sum of $q_s$ decreasing positive terms.
--
--   **Formalization Note** "Decreasing" is read strictly, as the paper writes "non-decreasing"/"non-increasing" when it means the weak notions (Proposition 1). $a_k$ uses the index-corrected convention of the definition file `FastFashion.Approx.Tangents`.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 12, §3.1.3, sentence after (5)

import Mathlib
import Definitions.Def_FastFashion_Approx_Tangents

namespace FastFashion.Approx

/-- The terms of the sums (4)–(5) (Caro–Gallien, p. 12) are positive and decreasing: for `λ > 0`
and `T > 0`, the slopes `a_k(λ) = γ(k+1, λT) / (λ k!)` satisfy `0 < a_k(λ)` and
`a_{k+1}(λ) < a_k(λ)` for every `k ∈ ℕ`. -/
theorem tangent_slopes_pos_decreasing (lam T : ℝ) (hlam : 0 < lam) (hT : 0 < T) (k : ℕ) :
    0 < a lam T k ∧ a lam T (k + 1) < a lam T k := by sorry

end FastFashion.Approx
