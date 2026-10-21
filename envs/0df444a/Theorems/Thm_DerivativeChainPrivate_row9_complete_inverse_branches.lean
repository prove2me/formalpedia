-- Prove2me | Theorems.Thm_DerivativeChainPrivate_row9_complete_inverse_branches
-- name    : DerivativeChainPrivate.row9_complete_inverse_branches
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T21:12:49.715693+00:00
-- url     : https://prove2.me/theorems/cb11729b-d642-4e08-b170-c7e80113e7fc
-- title:
--   Certified analytic cover of the row-9 inverse cubic
-- statement:
--   For the inverse cubic
--   $$G_9(t,v)=-2v^3+(168-42t)v^2+(-924+840t-168t^2+4t^3)v+1001-1716t+924t^2-168t^3+7t^4,$$
--   there exist real numbers $\alpha_1,\alpha_2,\alpha_3$ in the three explicit dyadic intervals in the formal statement, and functions $Y_i:\mathbb C\to\mathbb C$, holomorphic on $|t|<2$, such that
--   $$|Y_i(t)|\le10^{-14}\quad(|t|\le2),\qquad Y_i(t)\in\mathbb R\quad(t\in[-2,2]).$$
--   The intervals isolate the real roots at $t=0$ (approximately 1.468642, 4.359510, 78.171848); the approximations are explanatory only. If $|t|\le 10/7$ and $G(t,v)=0$, then for at least one $i\in\{1,2,3\}$,
--   $$v=P_{\alpha_i}(t)+t^{32}Y_i(t).$$
--   Here $P_\alpha$ is the explicit degree-at-most-31 polynomial in the certificate bundle. This gives a complete cover of the inverse roots in the region used by the derivative-chain proof.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; upper/H5_UPPER_BRIDGE.md, inverse cubic for row 9. This is an auxiliary exact certificate identity of the new Lean formalization; its coefficient arrays are fully specified in the accompanying fifth-power inverse-certificate definition bundle.

import Definitions.Def_DerivativeChainPrivate_fifth_row9_coefficient_bounds
import Definitions.Def_DerivativeChainPrivate_fifth_row9_inverse_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row9_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row9_separation
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row9_newton_inverse
import Theorems.Thm_DerivativeChainPrivate_row9_newton_residual
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.row9_complete_inverse_branches :
    ∃ a1 a2 a3 : ℝ, ∃ Y1 Y2 Y3 : ℂ → ℂ,
      ((57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a1 ∧ a1 ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ)) ∧ ((171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a2 ∧ a2 ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) ∧ ((770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ a3 ∧ a3 ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) ∧
      (DifferentiableOn ℂ Y1 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y1 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y1 (x:ℂ)).im=0)) ∧ (DifferentiableOn ℂ Y2 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y2 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y2 (x:ℂ)).im=0)) ∧ (DifferentiableOn ℂ Y3 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y3 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y3 (x:ℂ)).im=0)) ∧
      ∀ t : ℂ, ‖t‖ ≤ 10/7 → ∀ v : ℂ,
        row9G0 t+row9G1 t*v+row9G2 t*v^2+(-2)*v^3=0 →
        v=(row9P a1 t+t^32*Y1 t) ∨ v=(row9P a2 t+t^32*Y2 t) ∨ v=(row9P a3 t+t^32*Y3 t) := by sorry
