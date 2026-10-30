-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_proposition_4_2
-- name    : BrownSharedSignals.Fluid.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:54:13.240572+00:00
-- url     : https://prove2.me/theorems/b5709703-f5b2-4eab-8f45-5bf0513dbc6b
-- title:
--   Proposition 4.2 — Fluid and occupancy correspondences
-- statement:
--   For the finite shared-resource model, all four correspondences and bounds hold.
--
--   (a) Every optimal fluid schedule gives an optimal occupancy solution by $\mu_{t,i}(s,h,a)=q_t(h)u_{t,i}^*(s,h,a)$. Conversely, every optimal occupancy solution extends to an optimal fluid schedule whose controls at every positive-probability history equal $\mu^*/q_t(h)$.
--
--   (b) For every period, current signal and fluid state $f$, every joint initial distribution with local marginals $f_i$ satisfies $\mathbb E[V_t^*(\widetilde s,z)]\le V_t^F(f,z)$. Arbitrary correlations between initial project states are allowed.
--
--   (c) For every nonnegative history-dependent multiplier schedule,
--   $$V_t^F(f,z)\le \mathbb E[\sum_{\tau=t}^T\lambda_\tau(h_\tau)B_\tau(z_\tau)\mid h]+\sum_{i,s}f_i(s)L_{t,i}^\lambda(s,h).$$
--
--   (d) For any optimal LP (6) solution $(\lambda^*,\ell^*)$ and any optimal fluid schedule, the analogous affine upper bound using its project coordinates is an equality at the schedule’s fluid state at every rooted history, and that project-coordinate vector is a supergradient there. Optimal LP coordinates remain independent coordinates rather than being assumed equal to canonical Bellman values off their supported states. The printed universal-history scope is retained.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - encoding: finite-horizon expectations and maxima or minima → finite probability sums and real extrema of the operationally defined feasible value sets; reason: feasible action sets are finite and contain zero, and the finite-horizon LP and fluid feasible objectives have finite attained extrema on their stated domains
--   - encoding: current-signal notation abbreviating the fixed fluid or multiplier history → complete signal history is explicit, and fluid memory is computed from the fixed optimizer schedule; reason: the paper’s policies depend on this memory even when their displayed arguments suppress it
--   - encoding: conditioning on every rooted signal history → the forward project kernel along the fixed signal path, also on probability-zero histories; reason: this explicitly chooses a conditional-kernel version without adding a positive-history-probability assumption or removing null histories
--   - reading: Proposition 4.2(c) prints the joint-value symbol L_t on a local state → the project value L_{t,i} appears in the projectwise sum; reason: equation (5) and the same display in the proof on EC-7 determine the missing subscript
--   - encoding: any optimal solution written using Lagrangian value symbols in Proposition 4.2(d) → arbitrary optimal LP project coordinates are retained in the equality and supergradient; reason: the source quantifies over LP optimizers and does not force their unsupported coordinates to equal canonical Bellman values
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Proposition 4.2, printed 18–19 / PDF 19

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem proposition_4_2 {N T : ℕ} (M : Model N T) :
    (∀ u : Schedule M, OptimalSchedule M u → LP7Optimal M (scheduleOccupancy M u)) ∧
    (∀ μ : Occupancy M, LP7Optimal M μ →
      ∃ u : Schedule M, OptimalSchedule M u ∧
        ∀ t < T, ∀ h, 0 < historyProb M t h →
          ∀ i s a, u t h i s a = μ t h i s a / historyProb M t h) ∧
    (∀ t < T, ∀ (h : History M t) (f : FluidVector M), IsFluidState M f →
      ∀ ν : Arlib.Probability.FinDist (State M),
        (∀ i s, (∑ x : State M, if x i = s then ν x else 0) = f i s) →
        (∑ s, ν s * optimalValue M t h s) ≤ fluidValue M t f (current M h)) ∧
    (∀ lam : Multiplier M, NonnegativeMultiplier M lam →
      ∀ t < T, ∀ h f, IsFluidState M f →
        fluidValue M t f (current M h) ≤ penalty M lam t h +
          ∑ i, ∑ s, f i s * projectValue M lam t h i s) ∧
    (∀ lam ℓ, LP6Optimal M lam ℓ → ∀ u : Schedule M, OptimalSchedule M u →
      ∀ t < T, ∀ h, h 0 = M.initialSignal →
        fluidValue M t (scheduleState M u t h) (current M h) =
          penalty M lam t h + ∑ i, ∑ s, scheduleState M u t h i s * ℓ t h i s ∧
        Supergradient M t (current M h) (scheduleState M u t h) (ℓ t h)) := by sorry

end BrownSharedSignals.Fluid
