-- Prove2me | Theorems.Thm_EuclidDiamStream_lemma_3_8
-- name    : EuclidDiamStream.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:31.636367+00:00
-- url     : https://prove2.me/theorems/d7c88a99-89d6-479b-a1ac-80381ed6e595
-- title:
--   Lemma 3.8 — $V(d,\tau)=\exp(\Omega(\tau^2/d))$
-- statement:
--   There is an absolute constant $\kappa>0$ such that for all integers $0\le\tau\le d$ there is a real polynomial $q$ of degree at most $\tau$ with $|q(j)|\le1$ for $j\in\{1,\dots,d\}$ and
--   $$q(0)\ge\exp(\kappa\tau^2/d).$$
--   Equivalently, $V(d,\tau)\ge\exp(\kappa\tau^2/d)$, where $V(d,\tau)$ (Definition 3.6) is the maximum value of $q(0)$ over such polynomials.
--
--   The growth rate $\tau^2/d$ is what produces the exponent of the final space bound.
--
--   Differences from the source:
--   - encoding: V(d,τ) = exp(Ω(τ²/d)), V a maximum → ∃ κ > 0 absolute, ∀ τ ≤ d, ∃ admissible q with q(0) ≥ exp(κτ²/d); reason: equivalent to V ≥ exp(κτ²/d), and it avoids a real sSup, since V is unbounded at τ = d; "= exp(Ω(·))" is a lower bound
-- source:
--   Padaki, Singal, Waingarten, A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.12, Lemma 3.8 and p.11, Def. 3.6; proof p.13

import Mathlib

namespace EuclidDiamStream

/-- Lemma 3.8 of Padaki, Singal, Waingarten, *A Near-Optimal Space Lower Bound for Euclidean Diameter Estimation in Dynamic Streams*, arXiv:2609.19089 (held version of Nov 3, 2026, sha256 3fd06a3f…), p.12: `V(d,τ) = exp(Ω(τ²/d))`, where `V(d,τ)` (Definition 3.6, `τ ≤ d`) is the maximum of
`q(0)` over degree-`τ` polynomials with `|q(j)| ≤ 1` for `j ∈ {1,…,d}`.

**Formalization Note.** "`V = exp(Ω(·))`" is a lower bound, so the statement is that a polynomial of degree at
most `τ` that is admissible with `q(0) ≥ exp(κτ²/d)` exists, with `κ > 0` absolute. This is equivalent to
`V(d,τ) ≥ exp(κτ²/d)`, and it avoids a real `sSup` (`V` is unbounded at `τ = d`). At `d = 0` the division gives
`0`, and `q = 1` works. -/
theorem lemma_3_8 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ d τ : ℕ, τ ≤ d →
      ∃ q : Polynomial ℝ, q.natDegree ≤ τ ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ d → |q.eval (j : ℝ)| ≤ 1) ∧
        Real.exp (κ * (τ : ℝ) ^ 2 / (d : ℝ)) ≤ q.eval 0 := by sorry

end EuclidDiamStream
