-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_sixth_selected_sextic_step
-- name    : DerivativeChainPrivate.normalized_sixth_selected_sextic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:11:55.929421+00:00
-- url     : https://prove2.me/theorems/0784b977-aa0e-450f-9f6c-ca93707063c2
-- title:
--   A sixth-row step with its selected compact-measure inverse
-- statement:
--   Write $S_6(\beta,z)=(1360/91)\beta^2-20\beta z^3+(170/7)\beta z+z^6-5z^4+(85/16)z^2-1445/2184$, $\alpha_6=(455-3\sqrt{19565})/680$, $b_6=(559-3\sqrt{19565})/688$, $K_6=3\sqrt{19565}/680$. Assume $\Re\beta,\Im\beta\ge0$, $\Re w>0$, $\Im w\ge0$, $(\Re w)^2\ge5/2$, and $\beta/w=w^2/10-41/140+(459/7840)/(w^2-17/42)$. Also assume $w^5-(10/3)w^3-10\beta w^2+(85/48)w+(85/21)\beta=0$. Assume also $\Im\beta>0$. There exist a finite positive measure $\mu$, supported almost everywhere on $[-1/4,3/2]$ and representing the specified sexticShift as $\int(t-u)^{-1}d\mu$, and a root $z$ of $S_6$ northeast of $w$, with $\Im z>0$, $(\Re z)^2>7/2$, and $\beta/z=\alpha_6z^2-b_6+K_6\int(z^2-t)^{-1}d\mu$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/join56/SixthSelectedSexticStep.lean, lines 7-33, SHA-256 9396b480fbec1ed7a91dd7a4bcd02c980960906469b9a060f415307c3a42fe50.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators

theorem DerivativeChainPrivate.normalized_sixth_selected_sextic_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-(10/3)*w^3-10*β*w^2+(85/48)*w+(85/21)*β=0)
    (hwinv : β/w = (1/10:ℂ)*w^2-41/140+(459/7840:ℂ)/(w^2-17/42)) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      (∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2)) ∧
      (∀ u : ℂ, 0 < u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u =
        TeschlQM.Herglotz.borelTransform μ u) ∧
      ∃ z : ℂ,
        (1360/91)*β^2-20*β*z^3+(170/7)*β*z+z^6-5*z^4+(85/16)*z^2-1445/2184=0 ∧
        w.re ≤ z.re ∧ w.im ≤ z.im ∧ 0 < z.im ∧ 7/2 < z.re^2 ∧
        β/z = (((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*z^2-(((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
          ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) := by sorry
