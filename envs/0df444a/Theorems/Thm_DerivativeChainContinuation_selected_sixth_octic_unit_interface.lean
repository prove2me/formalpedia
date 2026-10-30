-- Prove2me | Theorems.Thm_DerivativeChainContinuation_selected_sixth_octic_unit_interface
-- name    : DerivativeChainContinuation.selected_sixth_octic_unit_interface
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:06:50.595167+00:00
-- url     : https://prove2.me/theorems/e8bdf61a-e126-41f4-94b4-0f986711161f
-- title:
--   The selected actual eighth-row root at its scaled physical point
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. Let $\rho=\sqrt{17/2}$, $\lambda=1/\rho$, and $\Gamma(\beta)=136\beta/\rho^3$. Write $S_8(\beta,z)=(5440/13)\beta^2z^2-(92480/429)\beta^2-56\beta z^5+(680/3)\beta z^3-(5780/39)\beta z+z^8-(28/3)z^6+(595/24)z^4-(1445/78)z^2+24565/13728$, $\alpha_8=(91-3\sqrt{429})/1360$, $b_8=13/55-27\sqrt{429}/4840$. For a correction $E$ at $z$ with positive coordinates, put $A=\Re E/\Re z$, $B=\Im E/\Im z$, $C=(3A-B)/2$. Assume $\Re\beta\ge0$, $\Im\beta>0$, $\Re w,\Im w>0$, $(\Re w)^2\ge4$, $(D^{10}F_\beta)(w)=0$ and $\beta/w=\alpha_8w^2-b_8+E_8(w)/w$. Set $v=\lambda w$, $\gamma=\Gamma(\beta)$, $E=16\lambda E_8(w)$. Then $\Re\gamma\ge0$, $\Im\gamma>0$, $\Re v,\Im v>0$, $(\Re v)^2>52/85$, and $D^{10}[(X^3-X-\gamma)^6](v)=0$. At this same point $\gamma/v=((91-3\sqrt{429})/10)v^2-(208/55-54\sqrt{429}/605)+E/v$, with $0<A\le18/125$, $B\le0$, $0\le C\le73/250$ and $(\Re v)^2-3(\Im v)^2\ge52/85$.
-- source:
--   Preserved formal source snapshot /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/sixth_power/join78/SixthOcticUnitInterface.lean, lines 8-81, SHA-256 94892048c311b540a8f54748a8382882ccd02af9aecbd8fde40f5c4a32119400.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SixthPhysicalNormalization
import Definitions.Def_DerivativeChainPrivate_SixthOcticErrorDerivative
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

theorem DerivativeChainContinuation.selected_sixth_octic_unit_interface (β w : ℂ) (hR : 0≤β.re) (hI : 0<β.im)
    (hx : 0<w.re) (hy : 0<w.im) (hX : 4≤w.re^2)
    (hactual : (derivative^[10] ((X^3-C (17/2)*X-136*C β)^6 : Polynomial ℂ)).eval w=0)
    (hgraph : β/w=(((91-3*Real.sqrt 429)/1360:ℝ):ℂ)*w^2-
      ((13/55-27*Real.sqrt 429/4840:ℝ):ℂ)+sixthOcticRemainder w/w) :
    let c:=sixthPhysicalScale
    let γ:=sixthPhysicalParameter β
    let v:=(c:ℂ)*w
    let E:=((16*c:ℝ):ℂ)*sixthOcticRemainder w
    0≤γ.re ∧ 0<γ.im ∧ 0<v.re ∧ 0<v.im ∧ 52/85<v.re^2 ∧
      (derivative^[10] ((X^3-X-C γ)^6 : Polynomial ℂ)).eval v=0 ∧
      γ/v=(((91-3*Real.sqrt 429)/10:ℝ):ℂ)*v^2-
        ((208/55-54*Real.sqrt 429/605:ℝ):ℂ)+E/v ∧
      0<E.re/v.re ∧ E.re/v.re≤18/125 ∧ E.im/v.im≤0 ∧
      0≤(3*(E.re/v.re)-E.im/v.im)/2 ∧ (3*(E.re/v.re)-E.im/v.im)/2≤73/250 ∧
      52/85≤v.re^2-3*v.im^2 := by sorry
