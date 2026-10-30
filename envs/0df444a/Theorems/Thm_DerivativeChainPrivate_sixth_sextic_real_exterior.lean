-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_sextic_real_exterior
-- name    : DerivativeChainPrivate.sixth_sextic_real_exterior
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T00:50:23.307645+00:00
-- url     : https://prove2.me/theorems/319c678b-3c5e-49aa-b38d-e61c9bf378ca
-- title:
--   Radicand positivity outside the sextic support interval
-- statement:
--   If real $x\le-1/4$ or $x\ge3/2$, then $x^2-(85/43)x+1445/1806+(24565/211302)/x>0$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/join56/SixthSexticMeasure.lean, lines 91-105, SHA-256 f19a7e37af0a4cf3b58735dffb2bd056564dcad32770885ad8b580768e3b3091.

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

theorem DerivativeChainPrivate.sixth_sextic_real_exterior (x : ℝ) (hx : x ≤ -1/4 ∨ 3/2 ≤ x) :
    0 < x^2+(-85/43)*x+1445/1806+(24565/211302)/x := by sorry
