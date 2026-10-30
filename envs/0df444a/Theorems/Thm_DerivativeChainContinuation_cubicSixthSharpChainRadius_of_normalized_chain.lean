-- Prove2me | Theorems.Thm_DerivativeChainContinuation_cubicSixthSharpChainRadius_of_normalized_chain
-- name    : DerivativeChainContinuation.cubicSixthSharpChainRadius_of_normalized_chain
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:02:27.334522+00:00
-- url     : https://prove2.me/theorems/a5893524-e7d8-4637-9e38-b07cae39498b
-- title:
--   Conditional sixth-power radius bound assuming all eighteen normalized rows
-- statement:
--   Write $F_\beta=(X^3-(17/2)X-136\beta)^6$; its ordinary row of degree $m$ is $(D^{18-m}F_\beta)(z)=0$. Assume SixthCompleteNormalizedChain: for every $\Re\beta\ge0$, $\Im\beta>0$, all eighteen ordinary rows admit a chain starting at zero, nondecreasing in both coordinates, with vertices 12 through 17 equal. For any monic complex cubic $q$ whose roots lie in a disk of center $o$ and radius $R\ge0$, there are eighteen actual roots $(D^{17-i}q^6)(z_i)=0$, starting at the cubic root centroid, ending at a root of $q$, with the final six vertices equal. There are two orthogonal unit axes on which both projected coordinates are nondecreasing, and the chain length is at most $((1+\sqrt{10})/3)R$. The normalized eighteen-row proposition remains an explicit unproved premise.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/SixthPowerAssemblyTarget.lean, lines 15-32, SHA-256 5e637a2e6a9182c8ba8755b21f3eafb55a7d01a69c30bb69497a45714bcda8cb.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SixthPowerAssemblyTarget
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

theorem DerivativeChainContinuation.cubicSixthSharpChainRadius_of_normalized_chain
    (hchain : SixthCompleteNormalizedChain)
    (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree=3)
    (o : ℂ) (R : ℝ) (hR : 0≤R) (hbound : ∀ x : ℂ,q.eval x=0 → ‖x-o‖≤R) :
    ∃ (z : Fin 18 → ℂ) (a b : ℂ),
      (∀ i,(derivative^[18-(i.val+1)] (q^6)).eval (z i)=0) ∧
      z 0=q.roots.sum/3 ∧ (∀ i : Fin 18, 12 ≤ i.val → z i=z 17) ∧ q.eval (z 17)=0 ∧
      ‖a‖=1 ∧ ‖b‖=1 ∧ (a*starRingEnd ℂ b).re=0 ∧
      Monotone (fun i => (a*z i).re) ∧ Monotone (fun i => (b*z i).re) ∧
      chainCost z≤((1+Real.sqrt 10)/3)*R := by sorry
