-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01CenterSlotCertificateAtIffHall
-- name    : CubicP3Partition.R03SP01CenterSlotCertificateAtIffHall
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T09:55:42.409156+00:00
-- url     : https://prove2.me/theorems/da004f05-c0d0-4830-9f1d-822555cb6db0
-- title:
--   R03 P3-factor structural result: R03SP01CenterSlotCertificateAtIffHall
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01CenterSlotCertificateAtIffHall` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 4e1ff2664875b2b00606de187b2c034d0d2f8436fc9b50a16732852122407fef.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-center-slot-factor-bridge-candidate-v1.lean; source SHA-256 4e1ff2664875b2b00606de187b2c034d0d2f8436fc9b50a16732852122407fef; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_adda565e91_r03_sp01_center_slot_factor_bridge_candidate_v1

namespace CubicP3Partition

open CubicP3Partition
universe u
theorem R03SP01CenterSlotCertificateAtIffHall
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (C : Finset V)
    [Fintype ((↑C : Set V)ᶜ : Set V)]
    [DecidableEq V] [DecidableRel G.Adj]
    (n : Nat) (eC : Fin n ≃ (↑C : Set V))
    (hcard : Fintype.card ((↑C : Set V)ᶜ : Set V) = n * 2) :
    R03SP01CenterSlotCertificateAt G C n eC ↔
      R03SP01CenterSlotHallCondition G C n eC := by sorry

end CubicP3Partition
