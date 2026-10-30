-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_sixth_sextic_step
-- name    : DerivativeChainPrivate.normalized_sixth_sextic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:08:56.237505+00:00
-- url     : https://prove2.me/theorems/f18cf28c-c99b-45f4-bfb1-8e65491aa740
-- title:
--   A fixed-parameter fifth-to-sixth row northeast step
-- statement:
--   Write $S_6(\beta,z)=(1360/91)\beta^2-20\beta z^3+(170/7)\beta z+z^6-5z^4+(85/16)z^2-1445/2184$, $\alpha_6=(455-3\sqrt{19565})/680$, $b_6=(559-3\sqrt{19565})/688$, $K_6=3\sqrt{19565}/680$. Assume $\Re\beta,\Im\beta\ge0$, $\Re w>0$, $\Im w\ge0$, $(\Re w)^2\ge5/2$, and $\beta/w=w^2/10-41/140+(459/7840)/(w^2-17/42)$. Also assume $w^5-(10/3)w^3-10\beta w^2+(85/48)w+(85/21)\beta=0$. There exists $z$ with $S_6(\beta,z)=0$, $\Re z\ge\Re w$, $\Im z\ge\Im w$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/join56/SixthSexticStep.lean, lines 9-57, SHA-256 e289e20815b4d8714e54df3fbb47423e3c371b3b8337029dfd56d0598a2509d0.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators

theorem DerivativeChainPrivate.normalized_sixth_sextic_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-(10/3)*w^3-10*β*w^2+(85/48)*w+(85/21)*β=0)
    (hwinv : β/w = (1/10:ℂ)*w^2-41/140+(459/7840:ℂ)/(w^2-17/42)) :
    ∃ z : ℂ,
      (1360/91)*β^2-20*β*z^3+(170/7)*β*z+z^6-5*z^4+(85/16)*z^2-1445/2184=0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im := by sorry
