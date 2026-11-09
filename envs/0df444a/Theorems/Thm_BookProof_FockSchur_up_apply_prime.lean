-- Prove2me | Theorems.Thm_BookProof_FockSchur_up_apply_prime
-- name    : BookProof.FockSchur.up_apply_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T08:04:23.057548+00:00
-- url     : https://prove2.me/theorems/e9f1ebaa-677c-4d80-89f4-7284070204a7
-- title:
--   BookProof.FockSchur.up_apply'
-- statement:
--   BookProof.FockSchur.up_apply'

-- Generated from ChapterFockSchurEsa.lean — theorem BookProof.FockSchur.up_apply'
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterSirkBandLedger
open BookProof.FockSecondQuantization
open BookProof.FockSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.YangMillsFriedrichs

noncomputable section

theorem BookProof.FockSchur.up_apply_prime (j : ℕ) (α : Conf) (i : ℕ) : up j α i = α i + if i = j then 1 else 0 := by sorry
