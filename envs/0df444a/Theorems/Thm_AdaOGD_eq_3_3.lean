-- Prove2me | Theorems.Thm_AdaOGD_eq_3_3
-- name    : AdaOGD.eq_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:36.133991+00:00
-- url     : https://prove2.me/theorems/922448b8-e8ae-44b0-87be-6098948a3f9d
-- title:
--   Display (3.3) — the sum of inverse step sizes is at most $\log(T+1)\sqrt{1+\max M}$
-- statement:
--   For the step sizes $\eta_i^{t+1}=(t+1)/\sqrt{1+\max\{M_i^1,\dots,M_i^t\}}$ of Algorithm 3,
--   $$
--   \sum_{t=1}^{T-1}\max_{1\le i\le N}\Big\{\frac1{\eta_i^{t+1}}\Big\}\ \le\ \log(T+1)\sqrt{1+\max_{1\le i\le N,\,1\le t\le T}\{M_i^t\}} .
--   $$
--
--   This bounds the noise term of Lemma 3.10 by the overall maximum of the draws.
--
--   Differences from the source:
--   - generalization: the draws $M_i^t$ of Algorithm 3 (i.i.d. Geometric($p_0$)), $T\ge1$ → every sample $\omega$, every family of natural numbers $M_i^t$ and every $T\in\mathbb N$; reason: the inequality is deterministic; it specializes to the algorithm's draws at every sample
--   - encoding: agents $\mathcal N$, $\max_{1\le i\le N}$ → agents `Fin N`, the real supremum over `Fin N`; reason: the same value for $N\ge1$; for $N=0$ both sides are $0$ or nonnegative
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, proof of Theorem 3.7, display (3.3), p.17

import Mathlib
import Definitions.Def_AdaOGD_eta

namespace AdaOGD

/-- Display (3.3) (Jordan, Lin & Zhou, arXiv:2310.14085v4, proof of Theorem 3.7, display (3.3),
p.17): for the step sizes `ηᵗ⁺¹ᵢ = (t + 1)/√(1 + max{M¹ᵢ, …, Mᵗᵢ})` of Algorithm 3,
`∑_{t=1}^{T−1} max_{1≤i≤N} 1/ηᵗ⁺¹ᵢ ≤ log(T + 1) √(1 + max_{1≤i≤N, 1≤t≤T} Mᵗᵢ)`.

**Formalization Note** The inequality is deterministic: it is stated for every sample `ω` and for
every family of natural-number draws `M` and every `T`, with no distributional assumption. `max_{1≤i≤N}` is the
real supremum over the finite index set `Fin N`. -/
theorem eq_3_3 {Ω : Type*} {N : ℕ} (M : Fin N → ℕ → Ω → ℕ) (T : ℕ) (ω : Ω) :
    ∑ t ∈ Finset.Icc 1 (T - 1), (⨆ i : Fin N, 1 / eta M i (t + 1) ω)
      ≤ Real.log ((T : ℝ) + 1) * Real.sqrt (1 + (maxDraw M T ω : ℝ)) := by sorry

end AdaOGD
