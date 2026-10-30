-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_sextic_selected_graph
-- name    : DerivativeChainPrivate.sixth_sextic_selected_graph
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:08:56.124247+00:00
-- url     : https://prove2.me/theorems/34d7f727-b3f5-4bd2-b711-5cd0d1511fdd
-- title:
--   The northeast sextic root selects the slow inverse
-- statement:
--   Write $S_6(\beta,z)=(1360/91)\beta^2-20\beta z^3+(170/7)\beta z+z^6-5z^4+(85/16)z^2-1445/2184$, $\alpha_6=(455-3\sqrt{19565})/680$, $b_6=(559-3\sqrt{19565})/688$, $K_6=3\sqrt{19565}/680$. Let $H(u)=u^2-(85/43)u+1445/1806+(24565/211302)/u$. Let $\mu$ be a finite positive measure supported almost everywhere on $[-1/4,3/2]$, representing $\operatorname{sexticShift}(-85/43,1445/1806,24565/211302;u)$ as $\int(t-u)^{-1}\,d\mu(t)$ for every $\Im u>0$. Assume $\Re\beta,\Im\beta\ge0$, $\Re w>0$, $\Im w\ge0$, $(\Re w)^2\ge5/2$, and $\beta/w=w^2/10-41/140+(459/7840)/(w^2-17/42)$. If $S_6(\beta,z)=0$, $\Im z>0$ and $\Re w\le\Re z$, then $\beta/z=\alpha_6z^2-b_6+K_6\int(z^2-t)^{-1}d\mu$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/join56/SixthSexticSelected.lean, lines 7-51, SHA-256 d90efe7b54cfdbf44cac6d0e57c8bea4489961ec1f47bf54e5f7e7a2601a1888.

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

theorem DerivativeChainPrivate.sixth_sextic_selected_graph (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β w z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwinv : β/w = (1/10:ℂ)*w^2-41/140+(459/7840:ℂ)/(w^2-17/42))
    (hxz : w.re ≤ z.re) (hzI : 0 < z.im)
    (hzroot : (1360/91)*β^2-20*β*z^3+(170/7)*β*z+z^6-5*z^4+(85/16)*z^2-1445/2184=0) :
    β/z = (((455-3*Real.sqrt 19565)/680:ℝ):ℂ)*z^2-(((559-3*Real.sqrt 19565)/688:ℝ):ℂ)+
      ((3*Real.sqrt 19565/680:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) := by sorry
