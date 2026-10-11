-- Prove2me | Theorems.Thm_BookProof_YangMillsAbelianEsa_triple_swap_prime
-- name    : BookProof.YangMillsAbelianEsa.triple_swap_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:19:48.516981+00:00
-- url     : https://prove2.me/theorems/48095b81-421a-492c-aa96-4fe93060d979
-- title:
--   BookProof.YangMillsAbelianEsa.triple_swap'
-- statement:
--   BookProof.YangMillsAbelianEsa.triple_swap'

-- Generated from ChapterYangMillsAbelianEsa.lean — theorem BookProof.YangMillsAbelianEsa.triple_swap'
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianEsa
open BookProof.YangMillsAbelianEsa



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs

noncomputable section

theorem BookProof.YangMillsAbelianEsa.triple_swap_prime {α : Type*} [AddCommMonoid α] {N D : ℕ} (F : Fin N → Fin D → Fin D → α) :
    ∑ i : Fin D, ∑ j : Fin D, ∑ m : Fin N, F m i j
      = ∑ m : Fin N, ∑ i : Fin D, ∑ j : Fin D, F m i j := by sorry
