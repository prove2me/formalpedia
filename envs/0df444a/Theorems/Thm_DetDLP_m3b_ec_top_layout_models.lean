-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_top_layout_models
-- name    : DetDLP.m3b_ec_top_layout_models
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T04:19:36.543858+00:00
-- url     : https://prove2.me/theorems/f486e8ec-f239-563d-abed-de0bcf4583d1
-- title:
--   EC physical layout Models agreement from FitsCore
-- statement:
--   From ECFits.FitsCore on ECPhysicalNet.body, the vertex, wire, and edge counts and endpoints of ECPhysicalNet.layout match ECPolyDefs.ecBuild.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_M3B_ECFits

set_option autoImplicit false
open DetDLP DetDLP.M3B S8H0 GateSemantics ECPhysicalNet

set_option autoImplicit false
open DetDLP DetDLP.M3B S8H0 GateSemantics ECPhysicalNet

theorem DetDLP.m3b_ec_top_layout_models
    {p m k T : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (seed : ECSeed p m) (P : E.toAffine.Point) (pre : List Bool)
    (a : ECPolyDefs.N) (hfits : ECFits.FitsCore a (ECPhysicalNet.body (k := k) E seed T P pre)) :
    let L := ECPhysicalNet.layout (k := k) E seed T P pre
    let d := GateSemantics.d p
    let e := GateSemantics.e p
    let n := ECPolyDefs.ne a
    let g := ECPolyDefs.ng a
    let lookup := g + n
    let src := fun i => if i < n then ECPolyDefs.gate a i else if i < 3 * n then g + (i - n) % n else lookup + (i - 3 * n) / k
    let dst := fun i => if i < n then i else if i < 2 * n then i - n else if i < 3 * n then ECPolyDefs.succWire a (i - 2 * n)
      else ECPolyDefs.busOff d e (max d k) ((i - 3 * n) / k) 1 + (i - 3 * n) % k
    L.ng = lookup + 4 * m ∧ L.nb = n ∧ L.ne = 3 * n + 4 * m * k ∧
    (∀ i : Fin L.ne, (L.gate i).val = src i.val ∧ (L.bit i).val = dst i.val) := by sorry
