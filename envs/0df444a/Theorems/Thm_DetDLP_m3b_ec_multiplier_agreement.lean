-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_multiplier_agreement
-- name    : DetDLP.m3b_ec_multiplier_agreement
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T01:12:02.974021+00:00
-- url     : https://prove2.me/theorems/72a201bc-3c4c-4775-84ba-a70ff824b078
-- title:
--   EC multiplier network agreement
-- statement:
--   The elliptic-curve polynomial multiplier network and its physical named-block multiplier have identical gate counts, wire counts, gate and signal addresses, and local Boolean tests under the specified register correspondence.
-- source:
--   Private WireKit EC agreement lemma; local proof Solutions/Sol_m3b_ec_multiplier_agreement.lean

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs

set_option autoImplicit false
open DetDLP DetDLP.M3B S8H0 RegisterMap NamedBlocks S8J
open HashRows

theorem DetDLP.m3b_ec_multiplier_agreement {s : RegisterMap.Shape} {d K off : ℕ} (hd : 1 ≤ d) (a b z : ECPolyDefs.Word) (A B Z : HashRows.Word s) (R : Fin (w3_fpMulLayout d hd).nb → Ref s) (hr : ∀ j, ECPolyDefs.reg (off+j.val) = ((R j).source.val,(R j).read false,(R j).read true)) (ha : ∀ j, a j = ((A j).source.val,(A j).read false,(A j).read true)) (hb : ∀ j, b j = ((B j).source.val,(B j).read false,(B j).read true)) (hz : ∀ j, z j = ((Z j).source.val,(Z j).read false,(Z j).read true)) : let q := ECPolyDefs.prod K d off a b z; let c := HashRows.product hd A B Z R; ECPolyDefs.ng q = c.core.A.ng ∧ ECPolyDefs.ne q = c.core.A.ne ∧ (∀ j : Fin c.core.A.ne, ECPolyDefs.gate q j.val=(c.core.A.gate j).val ∧ ECPolyDefs.signal q j.val=(c.name j).val) ∧ (∀ (g : Fin c.core.A.ng) (x : Fin c.core.A.ne → Bool), ECPolyDefs.check q g.val (((List.finRange c.core.A.ne).filter (fun j => decide (c.core.A.gate j=g))).map x) = c.core.t g (fun j => x j.val)) := by sorry
