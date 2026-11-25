-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_slot_fits
-- name    : DetDLP.m3b_ec_slot_fits
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T04:00:04.786914+00:00
-- url     : https://prove2.me/theorems/986ce338-96d2-5416-a399-5155a7038349
-- title:
--   EC 4m slot bank Fits agreement
-- statement:
--   The 4m repeated slotN blocks in ECPolyDefs match ECChainBlocks.manyB (4*m) (ECPhysicalNet.slotAt E seed T) under ECFits.Fits.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_M3B_ECFits

set_option autoImplicit false
open DetDLP DetDLP.M3B DetDLP.M3B.ECFits S8H0 GateSemantics ECPhysicalNet ECChainBlocks
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

set_option autoImplicit false
open DetDLP DetDLP.M3B DetDLP.M3B.ECFits S8H0 GateSemantics ECPhysicalNet ECChainBlocks
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m3b_ec_slot_fits
    (p m k T : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (seed : ECSeed p m) :
    let K := (ShapeOf p m k).size
    let d := GateSemantics.d p
    let e := GateSemantics.e p
    let w := busWidth p k
    let cs := [p, E.a₁.val, E.a₂.val, E.a₃.val, E.a₄.val, E.a₆.val]
    let sd := (List.finRange m).flatMap fun i =>
      [(seed i false).1.val + 1, (seed i false).2.val, (seed i true).1.val + 1, (seed i true).2.val]
    Fits (ECPolyDefs.copies (4 * m) (fun i => ECPolyDefs.slotN K p d e w (i * ECPolyDefs.slotSize d e w) T cs sd (i / 4)))
      (manyB (4 * m) (slotAt (k := k) E seed T)) := by sorry
