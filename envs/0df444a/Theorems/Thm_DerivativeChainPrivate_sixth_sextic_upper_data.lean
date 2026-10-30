-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_sextic_upper_data
-- name    : DerivativeChainPrivate.sixth_sextic_upper_data
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:02:30.590227+00:00
-- url     : https://prove2.me/theorems/04e2e9f2-f656-450f-9030-88bc450e1322
-- title:
--   Controlled sextic branch data in the upper half-plane
-- statement:
--   Write $S_6(\beta,z)=(1360/91)\beta^2-20\beta z^3+(170/7)\beta z+z^6-5z^4+(85/16)z^2-1445/2184$, $\alpha_6=(455-3\sqrt{19565})/680$, $b_6=(559-3\sqrt{19565})/688$, $K_6=3\sqrt{19565}/680$. Let $H(u)=u^2-(85/43)u+1445/1806+(24565/211302)/u$. Let $\mu$ be a finite positive measure supported almost everywhere on $[-1/4,3/2]$, representing $\operatorname{sexticShift}(-85/43,1445/1806,24565/211302;u)$ as $\int(t-u)^{-1}\,d\mu(t)$ for every $\Im u>0$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. At a root with positive coordinates and squared real part at least $5/2$, there are real $\alpha,b$ and complex $E$ such that $\alpha>1/20$, $\beta/z=\alpha z^2-b+E/z$ and $\Im(\beta/z)>0$. Either the slow branch has $\alpha=\alpha_6$, $b=b_6$, $E=K_6z\int(z^2-t)^{-1}d\mu$, $\alpha<1/10$, $1/15<41/140-b$, $C\ge0$; or $\alpha>9/10$, $b<3/2$, $-3/100\le A\le0$, $B\ge0$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/join56/SixthSexticUpperData.lean, lines 10-83, SHA-256 813f4b4f21f558aed18ad3bfca04427d39ec39f5db5f651c6601f2f4e42a4984.

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

theorem DerivativeChainPrivate.sixth_sextic_upper_data (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-85/43) (1445/1806) (24565/211302) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (β z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 5/2 ≤ z.re^2)
    (hroot : (1360/91)*β^2-20*β*z^3+(170/7)*β*z+z^6-5*z^4+(85/16)*z^2-1445/2184=0) :
    ∃ α b : ℝ, ∃ e : ℂ,
      1/20 < α ∧ β/z = (α:ℂ)*z^2-(b:ℂ)+e/z ∧ 0 < (β/z).im ∧
      ((α = (455-3*Real.sqrt 19565)/680 ∧ b = (559-3*Real.sqrt 19565)/688 ∧
        e = ((3*Real.sqrt 19565/680:ℝ):ℂ)*(z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)) ∧
        α < 1/10 ∧ 1/15 < 41/140-b ∧ 0 ≤ (3*(e.re/z.re)-e.im/z.im)/2) ∨
       (9/10 < α ∧ b < 3/2 ∧ -(3/100) ≤ e.re/z.re ∧ e.re/z.re ≤ 0 ∧ 0 ≤ e.im/z.im)) := by sorry
