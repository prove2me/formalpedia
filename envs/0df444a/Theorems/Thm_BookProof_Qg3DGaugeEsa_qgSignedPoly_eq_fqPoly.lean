-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_qgSignedPoly_eq_fqPoly
-- name    : BookProof.Qg3DGaugeEsa.qgSignedPoly_eq_fqPoly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T18:50:38.894933+00:00
-- url     : https://prove2.me/theorems/6bd04217-1a64-45e3-9dc1-8a7e485dc19c
-- title:
--   The Lean 4 theorem `qgSignedPoly_eq_fqPoly` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgSignedPoly_eq_fqPoly` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.qgSignedPoly_eq_fqPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
open BookProof.FullQuadratic
open BookProof.HermiteRelative
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
open BookProof.Qg3DGaugeEsa



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.Qg3DGaugeEsa.qgSignedPoly_eq_fqPoly (kappa : Fin 84 → ℝ) :
    qgSignedPoly kappa = fqPoly (qgFqP kappa) qgFqQ 0 0 0 := by sorry
