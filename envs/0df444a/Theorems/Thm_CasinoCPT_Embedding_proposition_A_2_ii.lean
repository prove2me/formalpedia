-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_proposition_A_2_ii
-- name    : CasinoCPT.Embedding.proposition_A_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:32.505552+00:00
-- url     : https://prove2.me/theorems/b8e74d7a-09cb-4054-9d5d-69a31c0388cf
-- title:
--   Proposition A.2 (ii), p. 45 — U^µ_t(x) = U^µ_{t+1}(x) when t and x have opposite parity
-- statement:
--   Let $\mu\in\mathcal P_0(\mathbb Z)$ and $U_t=U^\mu_t$. For every $t\in\mathbb N$ and $x\in\mathbb Z$,
--   $$U_t(x)=U_{t+1}(x)\quad\text{when $t$ is odd and $x$ is even, or when $t$ is even and $x$ is odd.}$$
--
--   The recursion (6) therefore updates only the nodes $(t,x)$ that the random walk can occupy at time $t-1$, mirroring the parity structure of the binomial tree.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 45, Proposition A.2 (ii)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- Proposition A.2 (ii), p. 45: for `μ ∈ 𝒫₀(ℤ)`, `U^μ_t(x) = U^μ_{t+1}(x)` when `t` is odd and
`x` is even, or when `t` is even and `x` is odd. -/
theorem proposition_A_2_ii (μ : Measure ℤ) (hμ : InP0Z μ) :
    ∀ (t : ℕ) (x : ℤ), ((Odd t ∧ Even x) ∨ (Even t ∧ Odd x)) →
      evol μ t x = evol μ (t + 1) x := by sorry

end CasinoCPT.Embedding
