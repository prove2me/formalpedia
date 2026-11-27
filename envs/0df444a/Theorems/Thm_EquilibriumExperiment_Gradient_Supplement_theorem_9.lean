-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_Supplement_theorem_9
-- name    : EquilibriumExperiment.Gradient.Supplement.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T06:19:15.6523+00:00
-- url     : https://prove2.me/theorems/274f55d3-cbe5-4ea2-8918-6d71742219c7
-- title:
--   Theorem 9 (companion theorem; not used in the proof of the goal) — quadratic mean-field utility cost
-- statement:
--   Fix a finite nonempty context family satisfying the published market assumptions, a compact positive payment interval $I=[c^-,c^+]$, and positive activation at every payment in that interval. There are constants $C>0$ and $\alpha>0$, with $\alpha<c^-$, such that for every integer $T\ge1$, every context path $(A_t)_{t=1}^T$, every payment sequence $p_t\in I$, and every $0\le\zeta<\alpha$,
--   $$\frac1T\sum_{t=1}^T\bigl(u_{A_t}(p_t)-u_{A_t}(p_t,\zeta)\bigr)\le C\zeta^2.$$
--   Here $u_a(p)$ is the published unperturbed mean-field utility, and $u_a(p,\zeta)$ is the mean-field utility at the actual equilibrium induced by the equiprobable payments $p\pm\zeta$. These constants depend on the market family and interval, and are independent of $\zeta$, $T$, the state path and the payments within that interval. In particular the bound applies pathwise to the source learning algorithm. It requires neither strong concavity nor Theorem 7.
--
--   **Formalization Note** The limit utility includes the full correlated payment expectation, not just an active-supply perturbation. The endpoint $\zeta=0$ is included. Compactness and positivity keep the equilibrium root away from zero locally uniformly; the second-derivative bounds in the source proof then yield constants uniform on the interval. The perturbation radius $\alpha$ is unrelated to the exponent in Theorem 6. No uniform gradient-consistency premise is introduced.
--
--   Differences from the source:
--   - generalization: the displayed average uses the algorithm payments p_t → the same bound holds for every sequence of payments in the fixed admissible interval; reason: the pointwise bound is uniform on that compact positive interval and therefore applies to every realized algorithm path.
--   - reading: conditions of Theorem 6 and the positive-payment algorithm interval → the frozen Standing and activation-positivity hypotheses hold for every state and payment in a fixed interval 0<lo≤hi; reason: these are the published base conventions applied over the payment domain; the radius is chosen below lo.
--   - encoding: u_a(p,ζ) is expected mean-field utility under symmetric perturbations → uPert uses the positive perturbed equilibrium and the correlated payment expectation; reason: equations (3.3), (3.6), (3.8)–(3.11) and Assumptions 1–3 give this limit without a finite-market revenue encoding.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 23, Theorem 9, (4.8); p. 40, Appendix A.7; p. 22, payment interval in §4.2

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Supplement_Learning
import Definitions.Def_EquilibriumExperiment_Gradient_Supplement_PerturbedUtility

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient.Supplement

theorem theorem_9 {A B : Type} [Fintype A] [Nonempty A] [MeasurableSpace B]
    (E : ContextFamily A B) (hE : ∀ a, (E.market a).Standing)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi)
    (hpos : ∀ a, ∀ p ∈ Set.Icc lo hi,
      0 < ∫ b, (E.market a).f b (p * (E.market a).omegaSup) ∂(E.market a).β) :
    ∃ C : ℝ, 0 < C ∧ ∃ radius : ℝ, 0 < radius ∧ radius < lo ∧
      ∀ T : ℕ, 1 ≤ T → ∀ states : Fin T → A, ∀ payments : Fin T → ℝ,
      (∀ t, payments t ∈ Set.Icc lo hi) → ∀ ζ ∈ Set.Ico (0 : ℝ) radius,
      (∑ t : Fin T, ((E.market (states t)).u (payments t) -
        uPert (E.market (states t)) (payments t) ζ)) / T ≤ C * ζ ^ 2 := by sorry

end EquilibriumExperiment.Gradient.Supplement
