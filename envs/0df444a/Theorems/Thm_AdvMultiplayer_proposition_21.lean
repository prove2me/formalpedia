-- Prove2me | Theorems.Thm_AdvMultiplayer_proposition_21
-- name    : AdvMultiplayer.proposition_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:17:03.306258+00:00
-- url     : https://prove2.me/theorems/7173e94a-3bb0-453b-9020-257a53a26090
-- title:
--   Proposition 21 — total stopped transport envelope
-- statement:
--   Throughout, the rewards are rounded, the identification array is arbitrary and fixed first, and probabilities are over the fresh-row law: independent complete rows, private tapes, and $J$ read from the coordinator's tape. For the fresh-row reference execution launched with zero scores,
--   $$\mathbb EJ_{\mathrm{stop}}\le C_{\mathrm{tr}}[(4m+128)\eta T+2],\qquad\Pr(\tau_{\mathrm{bad}}\le T)\le2N^{-2}.$$
--
--   Differences from the source:
--   - encoding: expectation of J_stop → `Integrable` is stated as a conclusion; reason: so that the integral is not a junk value
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Proposition 21, p.40, (42)

import Mathlib
import Definitions.Def_AdvMultiplayer_FreshRow

open MeasureTheory

namespace AdvMultiplayer

/-- **Proposition 21 (total stopped transport envelope).** Gan, arXiv:2610.05688, Proposition 21, p.40,
(42): `E J_stop ≤ C_tr[(4m+128)ηT + 2]` and `Pr(τ_bad ≤ T) ≤ 2N⁻²`, in the fresh-row reference
execution launched with zero scores.

**Formalization Note.** The tuned rate `η` is that of the construction branch; rewards are rounded. -/
theorem proposition_21 (p : Size) (hb : p.branch) (idA : IdArray p) (r : Rewards p)
    (hr : IsRounded p r) :
    Integrable (fun x => Jstop p (idA, x.1) r (freshTrace p idA r x)) (freshLaw p) ∧
    ∫ x, Jstop p (idA, x.1) r (freshTrace p idA r x) ∂(freshLaw p)
      ≤ p.Ctr * ((4 * (p.m : ℝ) + 128) * p.eta * p.T + 2) ∧
    freshLaw p {x | tauBad p (idA, x.1) (freshTrace p idA r x) ≤ p.T}
      ≤ ENNReal.ofReal (2 / (p.N : ℝ) ^ 2) := by sorry

end AdvMultiplayer
