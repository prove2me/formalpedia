-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row10_complete_inverse_branches
-- name    : DerivativeChainPrivate.row10_complete_inverse_branches
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T21:52:53.535995+00:00
-- url     : https://prove2.me/theorems/e982907b-a1b0-4987-bcaa-65624057fc1f
-- title:
--   Certified analytic cover of the row-10 inverse cubic
-- statement:
--   For the inverse cubic
--   $$G_{10}(t,v)=-60v^3+(1260-630t+30t^2)v^2+(-3960+5040t-1680t^2+120t^3)v+3003-6435t+4620t^2-1260t^3+105t^4-t^5,$$
--   there exist real numbers $\alpha_1,\alpha_2,\alpha_3$ in the three explicit dyadic intervals in the formal statement, and functions $Y_i:\mathbb C\to\mathbb C$, holomorphic on $|t|<2$, such that
--   $$|Y_i(t)|\le10^{-14}\quad(|t|\le2),\qquad Y_i(t)\in\mathbb R\quad(t\in[-2,2]).$$
--   The intervals isolate the real roots at $t=0$ (approximately 1.168822, 2.465889, 17.365289); the approximations are explanatory only. If $|t|\le 5/4$ and $G(t,v)=0$, then for at least one $i\in\{1,2,3\}$,
--   $$v=P_{\alpha_i}(t)+t^{32}Y_i(t).$$
--   Here $P_\alpha$ is the explicit degree-at-most-31 polynomial in the certificate bundle. This gives a complete cover of the inverse roots in the region used by the derivative-chain proof.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, inverse cubic for row 10. This is an auxiliary exact certificate identity of the new Lean formalization; its coefficient arrays are fully specified in the accompanying fifth-power inverse-certificate definition bundle.

import Definitions.Def_DerivativeChainPrivate_fifth_row10_coefficient_bounds
import Definitions.Def_DerivativeChainPrivate_fifth_row10_inverse_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row10_separation
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row10_newton_inverse
import Theorems.Thm_DerivativeChainPrivate_row10_newton_residual
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row10_complete_inverse_branches :
    ∃ a1 a2 a3 : ℝ, ∃ Y1 Y2 Y3 : ℂ → ℂ,
      ((23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ a1 ∧ a1 ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) ∧ ((97160973648365359300573924314704264662030400264262134485861186056383350158245991701430729829643120229512794018619323/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a2 ∧ a2 ≤ (24290243412091339825143481078676066165507600066065533621465296514095837539561497925357682457410780057378198504654831/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) ∧ ((342113602974777971780177930530474855198990249462270615508012205216651868652496554890450202993505122452981721333792045/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ a3 ∧ a3 ≤ (684227205949555943560355861060949710397980498924541231016024410433303737304993109780900405987010244905963442667584091/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) ∧
      (DifferentiableOn ℂ Y1 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y1 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y1 (x:ℂ)).im=0)) ∧ (DifferentiableOn ℂ Y2 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y2 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y2 (x:ℂ)).im=0)) ∧ (DifferentiableOn ℂ Y3 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y3 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y3 (x:ℂ)).im=0)) ∧
      ∀ t : ℂ, ‖t‖ ≤ 5/4 → ∀ v : ℂ,
        row10G0 t+row10G1 t*v+row10G2 t*v^2+(-60)*v^3=0 →
        v=(row10P a1 t+t^32*Y1 t) ∨ v=(row10P a2 t+t^32*Y2 t) ∨ v=(row10P a3 t+t^32*Y3 t) := by sorry
