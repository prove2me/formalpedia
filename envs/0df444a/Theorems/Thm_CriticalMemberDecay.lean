-- Prove2me | Theorems.Thm_CriticalMemberDecay
-- name    : CriticalMemberDecay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:32:45.701815+00:00
-- url     : https://prove2.me/theorems/efd7f122-1bd4-4b6e-8bd9-9d452a023641
-- title:
--   Critical Member Decay: Critical Member Decay
-- statement:
--   High-order decay at a critical member of the compact family.  If the jet `z`
--   belongs to `CompactJetFamily p` and its gradient component vanishes at the origin,
--   then there is a radius `ρ ∈ (0, 1/4)` on whose closed ball the function component of
--   `z` is bounded by `(1/2) * ρ ^ (k + β)`.
--
--   The factor `1/2` is the margin the paper's covering argument needs: it is what makes
--   the set of jets obeying the unhalved bound a NEIGHBOURHOOD of `z` in the jet metric.
--
--   The decay is obtained at the exponent `k + β'` for an auxiliary
--   `β' := (β + min 1 (SOpt p - k)) / 2` strictly between `β` and `1`, not at the
--   ambient `k + β`: degree-`k` vanishing together with mere `C^k` regularity gives only
--   `o(‖x‖^k)`, which does not beat `ρ ^ (k + β)`.  The extra room comes from the
--   qualitative Iwaniec-Manfredi regularity, which supplies `C^{k,β'}` for every
--   `k + β' < SOpt p`, and `k + β' > k + β` is what turns the bound strict.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CriticalMemberDecay.lean#L20-L128
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/CriticalMemberDecay.lean#L20-L128

import Definitions.Def_PHigherOrder_CompactJetFamilyPHarm
import Definitions.Def_PHigherOrder_Rigidity
import Definitions.Def_PHigherOrder_TaylorVanishingDecay
import Definitions.Def_PHigherOrder_IMRegularityInput
import Definitions.Def_PHigherOrder_CriticalMemberDecay
import Theorems.Thm_CompactJetFamilyPHarm
import Theorems.Thm_Rigidity
import Theorems.Thm_TaylorVanishingDecay

set_option autoImplicit false

theorem CriticalMemberDecay (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hL : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p)
    (z : BoundedContinuousFunction XHalf (ℝ × Plane)) (hz : z ∈ CompactJetFamily p)
    (hcrit : ∀ x : XHalf, (x : Plane) = 0 → (z x).2 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 4 ∧
      ∀ x : XHalf, ‖(x : Plane)‖ ≤ ρ → |(z x).1| < (1 / 2) * ρ ^ ((k : ℝ) + β) := by sorry
