-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_lemma_1
-- name    : EquilibriumExperiment.Gradient.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:29.319078+00:00
-- url     : https://prove2.me/theorems/3a4177f5-39d9-465f-a759-6ac338745b81
-- title:
--   Lemma 1, p. 18 — the equilibrium active supply size exists, is unique, and is Binomial
-- statement:
--   Fix a market satisfying the standing assumptions (Definition 5, Assumptions 1–3, (3.1)–(3.2)), a market size $n \ge 1$, and a payment distribution $\pi$, a probability measure on $\mathbb R_+ = [0,\infty)$. Let
--   $$\psi^{(n)}(\mu,\pi) = \mathbb E\bigl[f_{B_1}\bigl(P_1\,q^{(n)}(\mu)\bigr)\bigr], \qquad B_1 \sim \beta,\ P_1 \sim \pi,$$
--   be the probability that a supplier becomes active if it believes the active supply size is $\mathrm{Binomial}(n,\mu)$ (A.1). Then:
--   1. the balance equation $\psi^{(n)}(\mu,\pi) = \mu$ (A.2) has exactly one solution $\mu^{(n)}(\pi) \in [0,1]$;
--   2. when every supplier decides by the choice model (3.6) at this equilibrium, the number of active suppliers $T = \sum_{i=1}^n Z_i$ is $\mathrm{Binomial}(n, \mu^{(n)}(\pi))$: for $0 \le k \le n$,
--   $$\mathbb P(T = k) = \binom nk \mu^{(n)}(\pi)^k\bigl(1 - \mu^{(n)}(\pi)\bigr)^{n-k}.$$
--
--   This is the existence and uniqueness of the equilibrium on which every later quantity ($\mu^{(n)}(p)$, $\Delta^{(n)}(p)$, the perturbed equilibrium $\mu^{(n)}(p,\zeta)$) is built.
--
--   **Formalization Note** The paper's "Fix $p > 0$, $\zeta \in [0,p)$" is subsumed: $\pi_{p,\zeta}$ is a probability law on $\mathbb R_+$ for such $\zeta$, and the statement is made for every such law. The paper's proof reduces "exists, is unique" to the unique solvability of (A.2) in $[0,1]$ (p. 36); part 1 states exactly that, and part 2 states that the induced supply size is Binomial with that parameter. The supplier decisions are realized by independent uniforms, as described in the definitions file. The statement is conditional on the global state $A = a$.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 18, Lemma 1; proof in Appendix A.1, p. 36, (A.1)–(A.2)

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem lemma_1 {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    (π : Measure ℝ) [IsProbabilityMeasure π] (hπ : π (Set.Iio 0) = 0) {n : ℕ} (hn : 1 ≤ n) :
    (∃! μ : ℝ, μ ∈ Set.Icc (0 : ℝ) 1 ∧ M.psi n π μ = μ) ∧
    ∀ k : ℕ, k ≤ n →
      M.sample n π {x | ∑ i, M.Z n π x i = (k : ℝ)} =
        ENNReal.ofReal ((n.choose k : ℝ) * M.muN n π ^ k * (1 - M.muN n π) ^ (n - k)) := by sorry

end EquilibriumExperiment.Gradient
