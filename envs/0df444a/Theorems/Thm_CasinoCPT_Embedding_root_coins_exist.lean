-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_root_coins_exist
-- name    : CasinoCPT.Embedding.root_coins_exist
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T07:22:54.180877+00:00
-- url     : https://prove2.me/theorems/92d1cd35-8423-4998-85e3-a0a01d420b2e
-- title:
--   p. 15 — the Bernoulli coins ξ_{t,x} of a randomized Root time can be realised from F₀ on a casino space
-- statement:
--   Let $S$ be a standard symmetric random walk on a filtered probability space $(\Omega,\mathcal F,P;(\mathcal F_t))$ whose $\mathcal F_0$ carries a random variable $\xi$ uniformly distributed on $[0,1]$ (a casino space, §2.2). Let $b:\mathbb Z\to\mathbb N$ be any barrier and $r:\mathbb Z\to[0,1]$ any family of boundary probabilities. Then there is a family $\{\xi_{t,x}: t\in\mathbb N,\ x\in\mathbb Z\}$ of mutually independent, $\mathcal F_0$-measurable Bernoulli random variables with
--   $$P(\xi_{t,x}=0)=\begin{cases}0,& t<b(x),\\ r(x),& t=b(x),\\ 1,& t>b(x),\end{cases}$$
--   as required for the randomized Root stopping time (7). Moreover, the deterministic coins can be taken constant: $\xi_{t,x}\equiv1$ for $t<b(x)$, $\xi_{t,x}\equiv0$ for $t>b(x)$, and $\xi_{b(x),x}\equiv0$ whenever $r(x)=1$.
--
--   The paper uses this family on p. 15 without constructing it; the extra randomisation available in $\mathcal F_0$ (the uniform variable $\xi$) is what makes it possible.
--
--   **Formalization Note.** `coin t x ω = false` encodes $\xi_{t,x}=0$ ("stop"). The constancy clauses are stated everywhere, not only almost surely, so that the resulting Root time is bounded at every sample point.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 15 (randomized Root stopping times, family {ξ_{t,x}}, eq. (7)) and §2.2, p. 9 (uniform random variable on F₀)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- p. 15 (with §2.2, p. 9): on a casino space, for every barrier `b` and boundary probabilities
`r` with values in `[0, 1]`, the Bernoulli family `{ξ_{t,x}}` of the randomized Root stopping time
can be realised from `F 0`-information: there are `F 0`-measurable, mutually independent coins
with `P(ξ_{t,x} = 0) = 0, r(x), 1` for `t < b(x)`, `t = b(x)`, `t > b(x)`. Moreover the
deterministic coins can be chosen constant: `ξ_{t,x} ≡ 1` for `t < b(x)`, `ξ_{t,x} ≡ 0` for
`t > b(x)`, and `ξ_{b(x),x} ≡ 0` whenever `r(x) = 1`. -/
theorem root_coins_exist {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (b : ℤ → ℕ) (r : ℤ → ℝ) (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    ∃ coin : ℕ → ℤ → Ω → Bool, IsRootCoins P F b r coin ∧
      (∀ t x ω, t < b x → coin t x ω = true) ∧
      (∀ t x ω, b x < t → coin t x ω = false) ∧
      (∀ x ω, r x = 1 → coin (b x) x ω = false) := by sorry

end CasinoCPT.Embedding
