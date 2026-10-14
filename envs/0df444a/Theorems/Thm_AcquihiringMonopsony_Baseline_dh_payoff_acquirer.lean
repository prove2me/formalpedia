-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Baseline_dh_payoff_acquirer
-- name    : AcquihiringMonopsony.Baseline.dh_payoff_acquirer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:50.665834+00:00
-- url     : https://prove2.me/theorems/6790e457-c1a8-4f37-860f-e98c510df2ff
-- title:
--   Proof of Proposition 1, p. 6 — the acquirer's payoff from direct hiring is max{0, v_a − v_s − b}
-- statement:
--   In the baseline model with $b > 0$ and $\min\{v_a, v_s\} > b + \underline{w}$, consider any continuation equilibrium in undominated strategies of the direct-hiring subgame. The acquirer's equilibrium payoff is
--   $$
--   \max\{0,\ v_a - v_s - b\}.
--   $$
--
--   This is the first step of the proof of Proposition 1: it is the payoff from direct hiring that the acquirer compares with acquihiring.
--
--   **Formalization Note.** The statement covers every value of $v_a$, including the knife edge $v_a = v_s + b$, where both possible outcomes give the acquirer $0$.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 6 (PDF 7), §3, proof of Proposition 1, first sentence

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model

namespace AcquihiringMonopsony.Baseline

/-- Proof of Proposition 1 (p. 6), first sentence: in every continuation equilibrium of the
direct-hiring subgame the acquirer's payoff is `max {0, v_a − v_s − b}`. -/
theorem dh_payoff_acquirer (P : Params) (hP : P.Standing) (σ : DHProfile)
    (hσ : IsDHEquilibrium P σ) :
    dhPayoffA P σ.acceptA σ.wa σ.ws = max 0 (P.va - P.vs - P.b) := by sorry

end AcquihiringMonopsony.Baseline
