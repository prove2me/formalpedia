-- Prove2me | Theorems.Thm_BookProof_Qg3DGaugeEsa_qgSigned_eq_fqOp
-- name    : BookProof.Qg3DGaugeEsa.qgSigned_eq_fqOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T19:11:26.531991+00:00
-- url     : https://prove2.me/theorems/b08c7525-811b-4a16-96b6-efea343d9931
-- title:
--   The Lean 4 theorem `qgSigned_eq_fqOp` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgSigned_eq_fqOp` in the `ChapterQg3DGaugeEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQg3DGaugeEsa.lean

-- Generated from ChapterQg3DGaugeEsa.lean — theorem BookProof.Qg3DGaugeEsa.qgSigned_eq_fqOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterF7
open BookProof.FullQuadratic
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QuantumGravity3DGauge
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

set_option maxHeartbeats 4000000 in
-- the `L²` coercions of the Gauss–polynomial core make these defeq checks expensive

theorem BookProof.Qg3DGaugeEsa.qgSigned_eq_fqOp (kappa : Fin 84 → ℝ) :
    signedOp kappa (qgMom (coreRepPoly 84)) (torsionOps (coreRepPoly 84))
      = fqOp (qgFqP kappa) qgFqQ 0 0 0 := by sorry
