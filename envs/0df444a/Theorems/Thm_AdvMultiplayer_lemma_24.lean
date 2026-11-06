-- Prove2me | Theorems.Thm_AdvMultiplayer_lemma_24
-- name    : AdvMultiplayer.lemma_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:15:38.81424+00:00
-- url     : https://prove2.me/theorems/dd28bef8-ebcb-4019-9465-751350fa37ae
-- title:
--   Lemma 24 — local implementability and absence of domain errors
-- statement:
--   Use the construction-branch rate, and fix a table whose scalar coordinates lie in $[0,1)$. Suppose that, through round $t$, bootstrap states and activation times agree with the reference execution, every accepted ordinary message is the message currently sent on its channel, and the feasibility and stability bounds of Section 3 hold. Then every operation through round $t$ does not enter $\dagger$ and has inputs and outputs in its prescribed domains (61). At every assignment start $v\le t$, the coordinator's registers hold the exact calendar-round scores $Z(v)$ and queues $\mathsf B_v$, and every follower is unoccupied before the new assignment is issued.
--
--   Differences from the source:
--   - encoding: uses only information available to the player performing it → holds by the typing of `chooseProg` and `finishProg`; reason: their inputs are the player’s own, so nothing is left to state
--   - encoding: the coordinator knows Z(v) and the queues → register equality; reason: the meaning of “known” on p.31
--   - encoding: private draws → tape coordinates in [0,1); reason: the prescribed domain of a uniform draw, like the table’s
--   - reading: the feasibility and stability bounds of Section 3 → `RateOK`, w̄ ≤ w ≤ 2w̄ and β ≤ ξ ≤ 1/(16mK) on enabled rounds; reason: these are the bounds the proof of the lemma cites
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Lemma 24, p.51, (61)

import Mathlib
import Definitions.Def_AdvMultiplayer_FreshRow

namespace AdvMultiplayer

/-- **Lemma 24 (local implementability and absence of domain errors).** Gan, arXiv:2610.05688, Lemma
24, p.51, with the domains (61), p.52. A deterministic statement about one fixed execution prefix. With
the tuned rate, a table and tapes whose scalar coordinates lie in `[0,1)`, suppose that through round
`t` the bootstrap states and activation times agree with the reference execution, every accepted
ordinary message is the message currently sent on its channel, and the feasibility and stability bounds
of Section 3 hold. Then no operation through round `t` enters `†`, its quantities lie in their domains
(61), and at every assignment start `v ≤ t` the coordinator's registers are the calendar-round scores
`Z(v)` and queues `B_v`, and every follower is unoccupied.

**Formalization Note.** "Uses only information available to the player" holds by the typing of
`chooseProg` and `finishProg`, whose inputs are the player's own (`encoding`). The tape-domain hypothesis
states that the private draws lie in `[0,1)`, like the table's. -/
theorem lemma_24 (p : Size) (hb : p.branch) (d : TableData p)
    (hd : ∀ q s c, 0 ≤ d.2.2.1 q s c ∧ d.2.2.1 q s c < 1) (r : Rewards p) (hr : IsRewards p r)
    (ω : Tapes p) (hω : ∀ i s k, 0 ≤ ω i s k ∧ ω i s k < 1) (t : ℕ) (ht : t ∈ Finset.Icc 1 p.T)
    (hboot : ∀ s ∈ Finset.Icc 1 t, ∀ i,
      bootAgree p ((playRun p d r ω s).pre i)
        ((refRun p d r ω s).pre i))
    (hmsg : ∀ s ∈ Finset.Icc 1 t, ∀ dir k w,
      acceptedOn p (playRun p d r ω) s dir k w →
      curWord p (playRun p d r ω s).mid dir k = some w)
    (hrate : RateOK p p.eta)
    (hfeas : ∀ s ∈ Finset.Icc 1 t, enabledAt p (playRun p d r ω) s →
      ∀ a : Fin p.K,
        anchorAt p (playRun p d r ω) s a ≤
          calWeight p d (playRun p d r ω) s a ∧
        calWeight p d (playRun p d r ω) s a ≤
          2 * anchorAt p (playRun p d r ω) s a ∧
        p.betaOf p.eta ≤ (coAt p (playRun p d r ω) s).co.xi (a.val + 1) ∧
        (coAt p (playRun p d r ω) s).co.xi (a.val + 1) ≤
          1 / (16 * (p.m : ℝ) * (p.K : ℝ))) :
    (∀ s ∈ Finset.Icc 1 t, ∀ i,
      ((playRun p d r ω s).post i).dagger = false) ∧
    (∀ s ∈ Finset.Icc 1 t, ∀ j : Fin p.K,
      calArrival p d (playRun p d r ω) s j ≤ p.D ∧
      calService p d (playRun p d r ω) s j ≤ p.D) ∧
    (∀ v ∈ Finset.Icc 1 (t + 1), ∀ j : Fin p.K,
      calScore p d (playRun p d r ω) v j ≤ p.T * p.D ∧
      calQueue p d (playRun p d r ω) v j ≤ p.T * p.D ∧
      calScore p d (playRun p d r ω) v j +
          calQueue p d (playRun p d r ω) v j =
        ∑ s ∈ Finset.range v, calArrival p d (playRun p d r ω) s j) ∧
    (∀ s ∈ Finset.Icc 1 t, ∀ i,
      ((playRun p d r ω s).post i).fol.S ≤ p.T * p.D ∧
      ((playRun p d r ω s).post i).fol.b ≤ p.T * p.D ∧
      ((playRun p d r ω s).post i).fol.δ ≤ p.D ∧
      ((playRun p d r ω s).post i).fol.state ≤ 2) ∧
    (∀ s ∈ Finset.Icc 1 t, ∀ a,
      ((playRun p d r ω s).post (coordinator p)).co.acc a ≤ p.T * p.D) ∧
    (∀ s ∈ Finset.Icc 1 t, ∀ k,
      ((playRun p d r ω s).post (coordinator p)).co.P k = true →
        k ∈ Finset.Icc 1 p.d) ∧
    ∀ v ∈ Finset.Icc 1 t, assignStartAt p (playRun p d r ω) v →
      (∀ j : Fin p.K,
        (coAt p (playRun p d r ω) v).co.z (j.val + 1) =
          calScore p d (playRun p d r ω) v j) ∧
      (∀ j : Fin p.K,
        (coAt p (playRun p d r ω) v).co.Bq (j.val + 1) =
          calQueue p d (playRun p d r ω) v j) ∧
      ∀ i, i ≠ coordinator p →
        ((playRun p d r ω v).mid i).fol.state = 0 := by sorry

end AdvMultiplayer
