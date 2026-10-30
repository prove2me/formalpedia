-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_gini_disk_bound
-- name    : DerivativeChainContinuation.finite_gini_disk_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:42:23.056481+00:00
-- url     : https://prove2.me/theorems/378240a8-8c6f-43d1-8694-4167597a028e
-- title:
--   Gini dispersion bounded by containing-disk variance
-- statement:
--   Let $w_i\ge0$ sum to one, with complex barycenter $u$, and suppose every $z_i$ lies in the closed disk $D(a,D)$ with $D\ge0$. Then $$G(w,z)\le\sqrt{2(D^2-|u-a|^2)}.$$ The original containing-disk center is retained.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/GiniDiskBound.lean#L6-L39

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem DerivativeChainContinuation.finite_gini_disk_bound {ι : Type} [Fintype ι]
    (w : ι → ℝ) (z : ι → ℂ) (hw : ∀ i,0 ≤ w i) (hs : ∑ i,w i=1)
    (u a : ℂ) (D : ℝ) (hD : 0 ≤ D) (hm : ∑ i,(w i:ℂ)*z i=u)
    (hb : ∀ i,‖z i-a‖ ≤ D) :
    finiteGini w z ≤ Real.sqrt (2*(D^2-‖u-a‖^2)) := by sorry
