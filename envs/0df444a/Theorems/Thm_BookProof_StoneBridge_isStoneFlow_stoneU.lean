-- Prove2me | Theorems.Thm_BookProof_StoneBridge_isStoneFlow_stoneU
-- name    : BookProof.StoneBridge.isStoneFlow_stoneU
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:09:13.359972+00:00
-- url     : https://prove2.me/theorems/09674018-05cf-451b-be88-e7a449bccf4c
-- title:
--   The Lean 4 theorem `isStoneFlow_stoneU` in the `ChapterStoneBridge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `isStoneFlow_stoneU` in the `ChapterStoneBridge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneBridge.lean

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterYangMillsFriedrichs
-- Generated from ChapterStoneBridge.lean — theorem BookProof.StoneBridge.isStoneFlow_stoneU
import Mathlib
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterRitzCertificate
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterYangMillsHermite
open BookProof.StoneBridge






open Filter Topology
open scoped InnerProductSpace


open BookProof.FarisLavine BookProof.EsaClosure BookProof.YangMillsFriedrichs
open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]










variable [CompleteSpace F]

theorem BookProof.StoneBridge.isStoneFlow_stoneU (T : UnboundedSelfAdjoint F) : IsStoneFlow T T.stoneU := by sorry
