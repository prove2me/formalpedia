-- Prove2me | Theorems.Thm_DetDLP_m3d_ec_stage2_driver_with_order_tm
-- name    : DetDLP.m3d_ec_stage2_driver_with_order_tm
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T09:58:02.022366+00:00
-- url     : https://prove2.me/theorems/09dcb500-4499-433b-9c50-cdafd9b20ffb
-- title:
--   Elliptic Stage II driver with a curve-order oracle
-- statement:
--   Given the Stage I count oracle, factor-base subroutines, terminal network operations, and coset updates, a single deterministic machine solves the prime-order short Weierstrass driver specification. Its output certifies a bounded scan for small groups or a coset trace on native seed-indexed blocks for large groups, within the main time and space bounds.
-- source:
--   Order-aware variant of DetDLP.w3_ec_stage2_driver_tm; Stage I count interface DetDLP.M89S1.Query.ecOrder.

import Definitions.Def_DetDLP_W3_Driver
import Definitions.Def_DetDLP_M89_S1_Queries
set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m3d_ec_stage2_driver_with_order_tm
    (hord : DetDLP.M89S1.CountOracle)
    (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine) (do' : Fin de.tapeCount) (K : ℕ)
    (hnet : w3_terminalOps w3_ecQueries) (hupdate : w3_hnfOps) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
        letI := ecPointFintype E
        let M := Fintype.card E.toAffine.Point
        let m := blockCount (bitLen p)
        M.Prime → ∀ (P Q : E.toAffine.Point), addOrderOf P = M →
          let accepts := fun u => RunsWithin D out (encodeECDLPInput p E P Q) (countWord u)
                                    (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))
          (¬ w3_large p M → w3_scanOutput M P Q accepts) ∧
          (w3_large p M → ∀ F : Fin m → List E.toAffine.Point, w3_ecBaseCalls en eo de do' K E F →
            ∃ (seed : ECSeed p m) (B : Fin m → List E.toAffine.Point),
              (∀ i, (B i).Nodup ∧ (B i).toFinset = ecFactorBlock E (hashThreshold p (M-1) m M) seed i) ∧
              w3_traceOutput ⟨F⟩ ⟨B⟩ M P Q accepts) := by sorry
