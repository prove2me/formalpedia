-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_bus_agreement
-- name    : DetDLP.m3b_ec_bus_agreement
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T00:26:22.518015+00:00
-- url     : https://prove2.me/theorems/b4702878-a3d9-404f-980b-16cdcd73fc61
-- title:
--   Executable EC address buses agree with their physical named gate blocks
-- statement:
--   For every slot, the numeric bus has precisely the physical gates and incidences, sends each incidence to the same gate and register, and evaluates every local input in physical incidence order.
-- source:
--   Private formalization of the EC native wire programs: executable compiler and local tensor certificates.

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs
set_option autoImplicit false
open DetDLP DetDLP.M3B S8H0 RegisterMap NamedBlocks S8J ECPhysicalNet GateSemantics

theorem DetDLP.m3b_ec_bus_agreement {p m k : ℕ} (T : ℕ) (i : Fin (4*m)) :
    let a := ECPolyDefs.busN (ShapeOf p m k).size (d p) (e p) (busWidth p k) T i.val
    let I := inputs (p:=p) (m:=m) (k:=k)
    let b := ECAddrGadget.block T (I.parity i) (I.hash i) (I.selected i) (fun j => .reg (I.addr i j)) (I.carry i)
    ECPolyDefs.ng a=b.core.A.ng ∧ ECPolyDefs.ne a=b.core.A.ne ∧
    (∀ j : Fin b.core.A.ne, ECPolyDefs.gate a j.val=(b.core.A.gate j).val ∧ ECPolyDefs.signal a j.val=(b.name j).val) ∧
    (∀ (g : Fin b.core.A.ng) (x : Fin b.core.A.ne → Bool), ECPolyDefs.check a g.val (((List.finRange b.core.A.ne).filter (fun j => decide (b.core.A.gate j = g))).map x) = b.core.t g (fun j => x j.val)) := by sorry
