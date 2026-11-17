-- Prove2me | Theorems.Thm_ChoresEFX_Supplement_theorem_D_1
-- name    : ChoresEFX.Supplement.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:03:50.529207+00:00
-- url     : https://prove2.me/theorems/9ab9d954-3cfb-4ff4-8a7d-3c580a0a60b0
-- title:
--   Theorem D.1 — a four-agent, ten-chore instance whose optimal EFX factor is $\gamma>11/10$
-- statement:
--   There are nonnegative additive costs $c_i(g)$ for four agents and ten indivisible chores, and the real number $\gamma$ with
--   $$2\gamma^4+2\gamma^3-2\gamma^2-2\gamma-1=0,\qquad \gamma>\frac{11}{10},$$
--   such that the optimal EFX approximation factor of the instance is $\gamma$:
--
--   1. some complete allocation $Z$ is $\gamma$-EFX, i.e. $c_i(Z_i\setminus\{g\})\le\gamma\,c_i(Z_j)$ for all agents $i,j$ and all $g\in Z_i$;
--   2. no complete allocation is $\alpha$-EFX for any $\alpha<\gamma$.
--
--   So $\min_X\operatorname{rat}(X)=\gamma>11/10$: for additive chores, exact EFX can fail to exist, and even a $1.1$-EFX allocation need not exist. Theorem 1.3 of the paper is the introduction form of this result.
--
--   **Formalization Note** Agents are $\{0,1,2,3\}$, chores $\{0,\dots,9\}$, and a complete allocation is a map from chores to agents. The costs are real numbers: the paper's instance has the irrational entries $p=\gamma-1$, $\mu=1/\gamma-2p$, $\nu=\gamma(1+2p)-\mu$, and a rational instance cannot have the irrational optimal factor $\gamma$. Clause 2 is written as "$\alpha$-EFX implies $\gamma\le\alpha$".
--
--   Differences from the source:
--   - reading: "nonnegative additive-cost instance" (with §2's standing c_i into ℚ≥0) → real nonnegative costs c : Fin 4 → Fin 10 → ℝ; reason: the theorem's own instance (Table 3, p.24) has irrational costs and the irrational optimum γ, which no rational instance can have, so the §2 convention does not apply to D.1
--   - reading: "is γ > 11/10", with γ defined in §D.1 → ∃ γ with 11/10 < γ and 2γ⁴ + 2γ³ − 2γ² − 2γ − 1 = 0; reason: γ is the root named in §D.1, p.23; the polynomial pins it down (it is increasing on [1, ∞)), the stronger of the two readings
--   - encoding: optimal EFX approximation factor is γ → some σ is γ-EFX, and every α with some σ α-EFX has γ ≤ α; reason: min over the finitely many allocations of rat(σ) = inf{α ≥ 1 : σ α-EFX}; α-EFX sets are closed upward, and γ > 1
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cfae7201df0c48a376f019e1b4904b83856c5f916ac5f3c418207f4a89), Theorem D.1, p.23 (pdf p.23); proof pp.23–26 (Table 3 p.24, §D.3 p.26); Theorem 1.3, p.3

import Mathlib
import Definitions.Def_ChoresEFX_IsAlphaEFX

namespace ChoresEFX.Supplement

open ChoresEFX Finset

/-- **Theorem D.1 (EFX existence lower bound)**, p.23 (proof pp.23–26); Theorem 1.3, p.3, is its
introduction form.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…): "There is a nonnegative additive-cost instance with four agents
and ten chores whose optimal EFX approximation factor is γ > 11/10."

There are nonnegative additive costs `c` on four agents and ten chores and a real `γ`, the root
`> 11/10` of `2γ⁴ + 2γ³ − 2γ² − 2γ − 1 = 0` (§D.1, p.23), such that
1. some complete allocation is `γ`-EFX (§D.3, p.26), and
2. no complete allocation is `α`-EFX for any `α < γ` (§D.2, pp.24–26).

Together: `min_σ rat(σ) = γ`, the optimal EFX approximation factor.

**Formalization Note.** Agents are `Fin 4`, chores `Fin 10`, a complete allocation is `σ : Fin 10 → Fin 4`
(`ChoresEFX.bundle`). The costs are real: the paper's instance (Table 3, p.24) has the irrational entries
`p = γ − 1`, `µ = 1/γ − 2p`, `ν = γ(1+2p) − µ`, and no rational instance can have the irrational optimal
factor `γ` (the optimum of a rational instance is a ratio of rational costs). Clause 2 is written
`IsAlphaEFX c α σ → γ ≤ α`; since `γ > 1` this is `rat(σ) ≥ γ` with `rat(σ) = inf{α ≥ 1 : σ is α-EFX}`
(§2, p.5). -/
theorem theorem_D_1 :
    ∃ c : Fin 4 → Fin 10 → ℝ, (∀ i g, 0 ≤ c i g) ∧
      ∃ γ : ℝ, 11 / 10 < γ ∧ 2 * γ ^ 4 + 2 * γ ^ 3 - 2 * γ ^ 2 - 2 * γ - 1 = 0 ∧
        (∃ σ : Fin 10 → Fin 4, IsAlphaEFX c γ σ) ∧
        ∀ (σ : Fin 10 → Fin 4) (α : ℝ), IsAlphaEFX c α σ → γ ≤ α := by sorry

end ChoresEFX.Supplement
