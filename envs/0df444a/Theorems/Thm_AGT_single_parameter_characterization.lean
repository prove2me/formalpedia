-- Prove2me | Theorems.Thm_AGT_single_parameter_characterization
-- name    : AGT.single_parameter_characterization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:09:12.155394+00:00
-- url     : https://prove2.me/theorems/b774ac62-1efb-4407-bd23-b0e5abf552f3
-- title:
--   Truthful single-parameter mechanisms: monotone rules with critical-value payments
-- statement:
--   Normalized incentive compatible mechanisms on a single-parameter domain are exactly the monotone rules with critical-value payments — Theorem 9.36 of *Algorithmic Game Theory*, and this mission's goal. Bids are scalars in $[t_0, t_1]$; a player values winning alternatives (those in her win set $W_i$) at her bid and everything else at $0$; the mechanism is normalized: losing bids pay $0$. Then truthfulness holds if and only if both:
--
--   1. **monotonicity** — raising a winning bid, the others fixed, keeps it winning (Definition 9.34);
--   2. **critical-value payments** — for each player and each profile of the others' bids there is a value $c$ that every winning bid pays; and whenever some bid in $[t_0,t_1]$ loses, $c$ is the least upper bound of the losing bids — the threshold below which the player loses and above which she wins (Definition 9.35).
--
--   *A note on the rendering.* The book defines the critical value as $c_i(v_{-i}) = \sup\{v_i : f(v_i,v_{-i}) \notin W_i\}$ and flags it "undefined" when the player wins at every bid, requiring in that case only that winners pay some constant. The formal statement renders exactly this: the constant-payment clause always, the `IsLUB` clause guarded by nonemptiness of the losing set — no junk supremum anywhere. Quantifiers place $c$ after the player and the others' bids, so the critical value may depend on both, but not on the player's own bid.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 9.5.4, Definitions 9.33-9.35 and Theorem 9.36, pp. 228-230

import Definitions.Def_agt_mechanism

namespace AGT

/-- Normalized incentive compatible mechanisms on a single-parameter domain
are exactly the monotone rules with critical-value payments (Theorem 9.36
of *Algorithmic Game Theory*, the capstone of the mission).  Bids are
scalars in `[t₀, t₁]`; a player values winning alternatives at their bid
and everything else at `0`; the mechanism is normalized (losers pay `0`).
Then incentive compatibility holds if and only if

1. the rule is monotone — raising a winning bid keeps it winning — and
2. every winning bid pays a value `c` depending only on the others' bids,
   which, whenever some bid loses, is the critical value: the least upper
   bound of the losing bids.

The critical value is rendered through `IsLUB` guarded by nonemptiness of
the losing set, matching the book's caveat for the case where the player
wins at every bid (there the payment is merely some constant). -/
theorem single_parameter_characterization {A ι : Type*} [Fintype ι]
    [DecidableEq ι] (W : ι → Set A) (t0 t1 : ℝ) (h01 : t0 ≤ t1)
    (f : (ι → ℝ) → A) (p : ι → (ι → ℝ) → ℝ)
    (hnorm : SPNormalized W t0 t1 f p) :
    SPIncentiveCompatible W t0 t1 f p ↔
      SPMonotone W t0 t1 f ∧ SPCriticalPayments W t0 t1 f p := by
  sorry

end AGT
