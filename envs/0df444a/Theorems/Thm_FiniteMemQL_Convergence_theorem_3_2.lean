-- Prove2me | Theorems.Thm_FiniteMemQL_Convergence_theorem_3_2
-- name    : FiniteMemQL.Convergence.theorem_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:26.649739+00:00
-- url     : https://prove2.me/theorems/152fa523-ac3e-42af-a38b-6f309c412782
-- title:
--   Theorem 3.2, p. 11 — the approximate model's value differs from J*_β by at most ‖c‖∞/(1−β) Σ βᵗ L_t in expectation over the first window
-- statement:
--   Let $\pi_0^-$ be the prior of $X_0$, let $\pi^*$ be any probability measure on $\mathbb X$, and let a policy $\hat\gamma$ act on the first $N$ steps, producing the window $I_0^N=(Y_{[0,N]},U_{[0,N-1]})$. With $\hat z_0=(\pi_0^-,I_0^N)$ and $\tilde J^N_\beta(\hat z_0)=J^N_\beta(\pi^*,I_0^N)$,
--   $$
--   E^{\hat\gamma}_{\pi_0^-}\Bigl[\bigl|\tilde J^N_\beta(\hat z_0)-J^*_\beta(\hat z_0)\bigr|\Bigr]\le\frac{\|c\|_\infty}{1-\beta}\sum_{t=0}^\infty\beta^tL_t,
--   $$
--   with $L_t$ the filter-stability term (3.9). The optimal value of the approximate model is thus close to the true optimal value whenever the filter forgets its prior.
--
--   **Formalization Note** The paper writes the left side conditioned on $I_0^N$; its proof (Appendix B) bounds the expectation over $I_0^N$, which is what is stated: the sum over the observation histories $y_{[0,N]}$ weighted by their probabilities under $\pi_0^-$ and $\hat\gamma$. The policy on the first $N$ steps is any deterministic observation-history policy.
-- source:
--   Kara, Yüksel, Convergence of finite memory Q learning for POMDPs and near optimality of learned policies under filter stability, arXiv:2103.12158v4, p. 11, §3.2.1, Theorem 3.2 (proof: Appendix B, pp. 29–31)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace FiniteMemQL.Convergence

/-- Theorem 3.2, p. 11 (arXiv:2103.12158v4). Let `π₀` be the prior of `X_0`, let the history
policy `γ₀` act on the first `N` steps and produce the window `I₀ᴺ = (Y_{[0,N]}, U_{[0,N−1]})`.
Then, in expectation over `I₀ᴺ`,
`E[ |J̃^N_β(π₀, I₀ᴺ) − J*_β(π₀, I₀ᴺ)| ] ≤ ‖c‖∞ / (1 − β) Σ_t β^t L_t`,
where `J̃^N_β(π₀, I) = J^N_β(π*, I)` and `L_t` is (3.9). -/
theorem theorem_3_2 {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    (N : ℕ) (πs π₀ : Measure X) [IsProbabilityMeasure πs] [IsProbabilityMeasure π₀]
    (γ₀ : HistPolicy Y U) :
    ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ₀ ys *
        |JN M πs ((ys, histActs γ₀ ys) : Window Y U N) - JstarW M π₀ ((ys, histActs γ₀ ys) : Window Y U N)| ≤
      cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t := by sorry

end FiniteMemQL.Convergence
