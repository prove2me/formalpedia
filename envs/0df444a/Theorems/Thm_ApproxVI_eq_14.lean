-- Prove2me | Theorems.Thm_ApproxVI_eq_14
-- name    : ApproxVI.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:14:13.342285+00:00
-- url     : https://prove2.me/theorems/7cb739de-1f43-4bfb-9fa3-0f14a83c855f
-- title:
--   Theorem 2, proof, (14) — coupling bound $\|J_n-\hat J_n\|_\nu\le\|J_N-\hat J_N\|_\nu\vee\frac{2\epsilon}{1-\alpha}$ (corrected: $0\le a(n)\le1$)
-- statement:
--   Let $\nu$ be positive weights, $0<\alpha<1$, $T$ satisfy (AV1), $\epsilon>0$ and $N\in\mathbb N$. Let $(J_n)$ and $(\hat J_n)$ satisfy, for every $n\ge N$,
--
--   $$
--   J_{n+1}=J_n+a(n)\big[TJ_n-J_n+\epsilon_n+M_{n+1}\big],\qquad
--   \hat J_{n+1}=\hat J_n+a(n)\big[T\hat J_n-\hat J_n+\hat\epsilon_n+M_{n+1}\big],
--   $$
--
--   with the same noise $M_{n+1}$, errors $\|\epsilon_n\|_\nu\le\epsilon$, $\|\hat\epsilon_n\|_\nu\le\epsilon$, and step sizes $0\le a(n)\le1$. Then for every $n\ge N$,
--
--   $$
--   \|J_n-\hat J_n\|_\nu\le\|J_N-\hat J_N\|_\nu\ \vee\ \frac{2\epsilon}{1-\alpha}.\qquad(14)
--   $$
--
--   This bound shows that AVI stays within a bounded distance of its projective counterpart (12), which is assumption (A4) of the stability theorem.
--
--   Differences from the source:
--   - correction: a(n) ≥ 0 (AV4) → 0 ≤ a(n) ≤ 1 for n ≥ N; reason: the grouping step before (13) uses 1 − a(n+k) ≥ 0; counterexample without it: d = 1, Tx = x/2 (α = 1/2), ε = 1, a(N) = 3, J_N = Ĵ_N, ε_N = 1, ε̂_N = −1 gives ‖J_{N+1} − Ĵ_{N+1}‖ = 6 > 4 = max(0, 2ε/(1 − α)); since a(n) → 0 under (AV4) the bound holds eventually
--   - reading: Ĵ_{n+1} = Π_{B,C}(Ĵ_n + a(n)[TĴ_n − Ĵ_n + ε̂_n + M_{n+1}]) (12) → Ĵ follows the unprojected update for n ≥ N; reason: the displayed chain before (13) writes Ĵ_{n+k+1} as the unprojected update for n ≥ N; (14) is stated for that computation
--   - generalization: T is the Bellman operator (3), contractive by (AV1) → T is any map ℝ^d → ℝ^d satisfying (AV1); reason: the argument uses only (AV1); the Bellman operator under (AV1) is an instance
--   - generalization: sup_n ‖ε_n‖_ν ≤ ε and ε̂_n ≤ ε for all n; (AV2)–(AV5) → the error bounds only for n ≥ N; no assumption on M, the filtration or Σ a(n), Σ a(n)²; reason: (14) is a pathwise inequality for n ≥ N; the source's setting is an instance
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, Theorem 2, proof, (13)–(14), pp.16–17

import Mathlib
import Definitions.Def_ApproxVI_wNorm

namespace ApproxVI

/-- **Proof of Theorem 2, (13)–(14)**, Ramaswamy & Bhatnagar, *Analyzing Approximate Value
Iteration Algorithms*, arXiv:1709.04673v5, pp.16–17: let `J` follow the AVI recursion (5) and
`Ĵ` its counterpart (12) driven by the same noise `M`, with errors `‖εₙ‖_ν ≤ ε`,
`‖ε̂ₙ‖_ν ≤ ε` for `n ≥ N`. Then for any `n ≥ N`,
`‖Jₙ − Ĵₙ‖_ν ≤ ‖J_N − Ĵ_N‖_ν ∨ (2ε/(1 − α))` (14).

Hypotheses: (AV1) (§3.1, p.7), `ε > 0`, and for every `n ≥ N` the two recursions, the two
error bounds, and `0 ≤ a(n) ≤ 1`.

**Formalization Note** `Ĵ` follows the unprojected update for `n ≥ N`, as the displayed chain
before (13) computes it. The bound `a(n) ≤ 1` corrects the page: the grouping step before
(13) uses `1 − a(n + k) ≥ 0`, and (14) fails without it (`d = 1`, `T x = x/2`, `ε = 1`,
`a(N) = 3`, `J_N = Ĵ_N`, `ε_N = 1`, `ε̂_N = −1` gives `6 > 4`); since `a(n) → 0` under (AV4),
it holds eventually. -/
theorem eq_14 {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (T : (Fin d → ℝ) → (Fin d → ℝ))
    (hT : ∀ x y, wNorm ν (T x - T y) ≤ α * wNorm ν (x - y)) (ε : ℝ) (hε : 0 < ε)
    (a : ℕ → ℝ) (J Jh e eh M : ℕ → Fin d → ℝ) (N : ℕ)
    (hJ : ∀ n ≥ N, J (n + 1) = J n + a n • (T (J n) - J n + e n + M (n + 1)))
    (hJh : ∀ n ≥ N, Jh (n + 1) = Jh n + a n • (T (Jh n) - Jh n + eh n + M (n + 1)))
    (he : ∀ n ≥ N, wNorm ν (e n) ≤ ε) (heh : ∀ n ≥ N, wNorm ν (eh n) ≤ ε)
    (ha : ∀ n ≥ N, 0 ≤ a n ∧ a n ≤ 1) :
    ∀ n ≥ N, wNorm ν (J n - Jh n) ≤ max (wNorm ν (J N - Jh N)) (2 * ε / (1 - α)) := by sorry

end ApproxVI
