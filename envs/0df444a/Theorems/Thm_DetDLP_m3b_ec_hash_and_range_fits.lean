-- Prove2me | Theorems.Thm_DetDLP_m3b_ec_hash_and_range_fits
-- name    : DetDLP.m3b_ec_hash_and_range_fits
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T05:51:57.582045+00:00
-- url     : https://prove2.me/theorems/5df22d84-1f3b-4f5f-bf8f-865bdb4075c6
-- title:
--   Slot hash and range agreement
-- statement:
--   The rewired range bank and each rewired hash block fit their polynomial blocks when the input operand bits agree.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECPhysicalNet
import Definitions.Def_DetDLP_M3B_ECPolyDefs
import Definitions.Def_DetDLP_M3B_ECFits

open DetDLP DetDLP.M3B DetDLP.M3B.ECFits S8H0 RegisterMap NamedBlocks ECPhysicalNet ECArithBlock GateSemantics

theorem DetDLP.m3b_ec_hash_and_range_fits (p m k : ℕ) [Fact p.Prime] (i : Fin (4*m)) :
    let K := (ShapeOf p m k).size; let D := d p; let t := i.val*ECPolyDefs.slotSize D (e p) (busWidth p k)
    let r := fun g : ℕ => t+ECPolyDefs.pt D+g*ECPolyDefs.run D (e p)
    let ax := fun g : ℕ => r 7+g*ECPolyDefs.aux D
    let f := bankName (p:=p) (k:=k) i
    let bit := fun z : Ref (Sh p) => ((f z.source).val,z.read false,z.read true)
    Fits (ECPolyDefs.cat (ECPolyDefs.pbound K p D t) (ECPolyDefs.copies 7 (fun g => ECPolyDefs.gbound K p D (r g)))) (rewire (RangeRows.block D (e p) p) f) ∧
    ∀ (g : Fin 7) (c : GateRoutes.Coeff) (a x b : ECPolyDefs.Word) (A X B : HashRows.Word (Sh p)),
      (∀ j, a j = bit (A j)) → (∀ j, x j = bit (X j)) → (∀ j, b j = bit (B j)) →
      Fits (ECPolyDefs.hash K p D (e p) (r g) (ax g) a x b) (rewire (HashRows.block p { GateRoutes.wires (hd p) p c g with a := A, x := X, b := B }) f) := by sorry
