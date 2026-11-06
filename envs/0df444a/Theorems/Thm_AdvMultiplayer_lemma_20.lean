-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_20
-- name    : AdvMultiplayer.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:15:51.819602+00:00
-- url     : https://prove2.me/theorems/929ffc35-386c-456c-b993-cb9eff1a3fe1
-- title:
--   Lemma 20 — conditional cost of one transfer
-- statement:
--   Throughout, the rewards are rounded, the identification array is arbitrary and fixed first, and probabilities are over the fresh-row law: independent complete rows, private tapes, and $J$ read from the coordinator's tape. For a transfer starting at a stopping time $s$, with phases truncated immediately after the first decoder failure or queue-overflow update, including that round, or at the horizon,
--   $$\mathbb E[J_s\mid\mathcal F_s]\le C_{\mathrm{tr}}.$$
--
--   Differences from the source:
--   - encoding: a transfer starting at a stopping time s → a stopping time at a transfer start, or T+1 when absent; reason: an absent transfer has zero charge, as in the proof of Prop. 21
--   - encoding: conditional expectation of J_s → `Integrable` is stated as a conclusion; reason: so that the conditional expectation is not a junk value
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 20, p.39, (41)

import Mathlib
import Definitions.Def_AdvMultiplayer_FreshRow

open MeasureTheory

namespace AdvMultiplayer

/-- **Lemma 20 (conditional cost of one transfer).** Gan, arXiv:2610.05688, Lemma 20, p.39, (41). In the
fresh-row reference execution, for a transfer starting at a stopping time `s`, with phases `C, D, R`
truncated immediately after the first decoder failure or queue-overflow update, including that round, or
at the horizon: `E[J_s | ℱ_s] ≤ C_tr`.

**Formalization Note.** `s` is a stopping time of the pre-round histories, with value at most `T` only at
a transfer start; `T + 1` means the transfer is absent, and then `J_s = 0`. Rewards are rounded. `J_s` is
integrable, so the conditional expectation is not a junk value. -/
theorem lemma_20 (p : Size) (hb : p.branch) (idA : IdArray p) (r : Rewards p) (hr : IsRounded p r)
    (s : FreshΩ p → ℕ) (hs : IsStoppingTime (preRound p) fun x => ((s x : ℕ) : WithTop ℕ))
    (hstart : ∀ x, s x ≤ p.T → transferStartAt p (freshTrace p idA r x) (s x))
    (habsent : ∀ x, p.T < s x → s x = p.T + 1) :
    Integrable (fun x => Jcharge p (idA, x.1) r (freshTrace p idA r x) (s x)) (freshLaw p) ∧
    ((freshLaw p)[fun x => Jcharge p (idA, x.1) r (freshTrace p idA r x) (s x) | hs.measurableSpace])
      ≤ᵐ[freshLaw p] fun _ => p.Ctr := by sorry

end AdvMultiplayer
