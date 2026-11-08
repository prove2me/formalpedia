-- Prove2me | Theorems.Thm_EuclidDiamStream_lemma_3_7
-- name    : EuclidDiamStream.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:57.097772+00:00
-- url     : https://prove2.me/theorems/86f776f6-e4fd-4a6a-be8d-c7d053e8081b
-- title:
--   Lemma 3.7 — a matrix equal to $1$ outside the balls with $\|M\|_{\mathrm{op}}\le2^d/(1+V(d,\tau))$
-- statement:
--   Let $q$ be a real polynomial of degree at most $\tau$ with $|q(j)|\le1$ for $j\in\{1,\dots,d\}$ and $q(0)>-1$. Then there is a $2^d\times2^d$ matrix $M$ with $M_{z,x}=1$ whenever $z\notin\mathcal B(x,\tau)$ and
--   $$\|M\|_{\mathrm{op}}\le\frac{2^d}{1+q(0)}.$$
--   The source states this at $q(0)=V(d,\tau)$, the maximum of $q(0)$ over such polynomials (Definition 3.6).
--
--   The lemma converts a spectral question on the hypercube into a question about one extremal polynomial.
--
--   Differences from the source:
--   - generalization: ‖M‖_op ≤ 2^d/(1 + V(d,τ)), V the maximum of q(0) (Def. 3.6) → for every admissible q with q(0) > −1, some M has ‖M‖ ≤ 2^d/(1 + q(0)); reason: a maximizer q gives the printed form; V is unbounded at τ = d, where a real sSup would return the junk value 0
--   - encoding: ‖M‖_op → ‖M‖ with Matrix.Norms.L2Operator; reason: Mathlib's default matrix norm is entrywise; the scoped instance is the ℓ2 operator norm
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.11, Lemma 3.7 and Def. 3.6; proof pp.11–12

import Mathlib
import Definitions.Def_EuclidDiamStream_hamBall

open scoped Matrix.Norms.L2Operator

namespace EuclidDiamStream

/-- Lemma 3.7 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.11: there is a `2^d × 2^d` matrix `M` with `M_{z,x} = 1` whenever `z ∉ B(x,τ)` and
`‖M‖_op ≤ 2^d/(1 + V(d,τ))`, where `V(d,τ)` (Definition 3.6) is the maximum of `q(0)` over degree-`τ` polynomials
with `|q(j)| ≤ 1` for `j ∈ {1,…,d}`.

**Formalization Note.** `V(d,τ)` is not a real number when `τ = d` (the polynomial `a ∏_{j=1}^d (X − j)` has
`q(j) = 0` and any `q(0)`), so a real `sSup` would return the junk value `0`. The statement holds for every
admissible `q` with `q(0) > −1`, and a maximizer gives the printed form. `‖M‖` is the `ℓ2` operator norm
(`Matrix.Norms.L2Operator`). -/
theorem lemma_3_7 (d τ : ℕ) (q : Polynomial ℝ) (hq : q.natDegree ≤ τ)
    (hbound : ∀ j : ℕ, 1 ≤ j → j ≤ d → |q.eval (j : ℝ)| ≤ 1) (hq0 : -1 < q.eval 0) :
    ∃ M : Matrix (Cube d) (Cube d) ℝ,
      (∀ x z, τ < ham x z → M z x = 1) ∧
      ‖M‖ ≤ 2 ^ d / (1 + q.eval 0) := by sorry

end EuclidDiamStream
