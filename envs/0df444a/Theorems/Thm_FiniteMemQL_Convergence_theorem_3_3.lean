-- Prove2me | Theorems.Thm_FiniteMemQL_Convergence_theorem_3_3
-- name    : FiniteMemQL.Convergence.theorem_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:57.741984+00:00
-- url     : https://prove2.me/theorems/f4a6f916-e1a5-443b-a91c-cbbcaa3fabb6
-- title:
--   Theorem 3.3, p. 12 — the approximate model's optimal window policy loses at most 2‖c‖∞/(1−β) Σ βᵗ L_t in expectation over the first window
-- statement:
--   Let $\phi^N$ be an optimal policy of the approximate model, i.e. it attains the minimum in (3.7), extended to the finite-window belief MDP by $\tilde\phi^N(\pi,I)=\phi^N(\pi^*,I)$. Let $\pi_0^-$ be the prior of $X_0$ and let a policy $\hat\gamma$ act on the first $N$ steps. With $\hat z_0=(\pi_0^-,I_0^N)$,
--   $$
--   E^{\hat\gamma}_{\pi_0^-}\Bigl[\bigl|J_\beta(\hat z_0,\tilde\phi^N)-J^*_\beta(\hat z_0)\bigr|\Bigr]\le\frac{2\|c\|_\infty}{1-\beta}\sum_{t=0}^\infty\beta^tL_t .
--   $$
--   Applying the window policy computed for the approximate model to the true system therefore loses at most a multiple of the discounted filter-stability error.
--
--   **Formalization Note** As in Theorem 3.2, the conditioning on $I_0^N$ is read as the expectation over $I_0^N$ (what Appendix C proves). Optimality of $\phi^N$ is stated as attainment of the minimum in (3.7) for the value-iteration limit $J^N_\beta$.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, p. 12, §3.2.2, Theorem 3.3 (proof: Appendix C, pp. 31–32)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence

/-- Theorem 3.3, p. 12 (arXiv:2103.12158v4). Let `φ^N` be an optimal policy of the approximate model
(it attains the minimum in (3.7)), extended to the finite-window belief MDP by `φ̃^N(π, I) = φ^N(I)`.
Let `π₀` be the prior of `X_0` and let the history policy `γ₀` act on the first `N` steps. Then,
in expectation over `I₀ᴺ`,
`E[ |J_β((π₀, I₀ᴺ), φ̃^N) − J*_β(π₀, I₀ᴺ)| ] ≤ 2‖c‖∞ / (1 − β) Σ_t β^t L_t`. -/
theorem theorem_3_3 {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    (N : ℕ) (πs π₀ : Measure X) [IsProbabilityMeasure πs] [IsProbabilityMeasure π₀]
    (γ₀ : HistPolicy Y U) (φN : Window Y U N → U)
    (hφ : ∀ I : Window Y U N, Cstar M πs I (φN I) +
      M.β * ∑ y : Y, Pstar M πs I (φN I) y * JN M πs (shift I (φN I) y) = JN M πs I) :
    ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ₀ ys *
        |Jpol M φN (π₀, ((ys, histActs γ₀ ys) : Window Y U N)) -
          JstarW M π₀ ((ys, histActs γ₀ ys) : Window Y U N)| ≤
      2 * cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t := by sorry

end FiniteMemQL.Convergence
