-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_physical_offsets
-- name    : DetDLP.m3b_ec_physical_offsets
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T23:59:18.42282+00:00
-- url     : https://prove2.me/theorems/3996897c-1160-4c30-9c45-284e00bffab7
-- title:
--   Exact physical EC register sizes and lookup bus offsets
-- statement:
--   Flattening the slot, chain, and terminal shapes gives the stated register count. For each slot, bus and bit, the row-major flat address equals the slot offset plus the local bus offset and bit index.
-- source:
--   Private formalization of the EC native wire programs: executable compiler and local tensor certificates.

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
set_option autoImplicit false
open DetDLP DetDLP.M3B S8H0 RegisterMap GateSemantics ECPhysicalNet ECChainBlocks

theorem DetDLP.m3b_ec_physical_offsets (p m k : ℕ) :
    let d := GateSemantics.d p; let e := GateSemantics.e p; let w := busWidth p k
    let tr := 3*d+1; let pt := 1+2*tr; let run := 2*tr+d+2*(2*d+e)+1; let aux := 2*d+3*(d+1)
    let gs := run+aux; let bank := pt+7*run+7*aux; let slot := bank+d+(d+1)+3*w
    (ShapeOf p m k).size = 4*m*slot+2*((2*m+1)*(pt+4*gs)+2*m*(pt+2*(1+tr)+d+15*gs))+pt ∧
     ∀ (i : Fin (4*m)) (l : Fin 3) (j : Fin (busWidth p k)), (busAddr i l j).index.val = i.val*slot+bank+d+(d+1)+l.val*w+j.val := by sorry
