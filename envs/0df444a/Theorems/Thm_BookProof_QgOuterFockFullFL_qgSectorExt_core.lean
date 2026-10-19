-- Prove2me | Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorExt_core
-- name    : BookProof.QgOuterFockFullFL.qgSectorExt_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:54:11.394105+00:00
-- url     : https://prove2.me/theorems/aee38822-f00e-4e7a-a610-fed4c97f4d92
-- title:
--   `BookProof.QgOuterFockFullFL.qgSectorExt_core` (n : ℕ) (p : polyGaussCore (d := n * 84)) (h : (p : L2d (n * 84)) ∈ (harmFried (n * 84)).dom) : qgSectorExt n ⟨(p : L2d (n * 84)), h⟩
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockFullFL`.
--
--   `BookProof.QgOuterFockFullFL.qgSectorExt_core` (n : ℕ) (p : polyGaussCore (d := n * 84)) (h : (p : L2d (n * 84)) ∈ (harmFried (n * 84)).dom) : qgSectorExt n ⟨(p : L2d (n * 84)), h⟩ = qgSectorHam n p
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockFullFL.qgSectorExt_core`.

-- Generated from ChapterQgOuterFockFullFL.lean — theorem BookProof.QgOuterFockFullFL.qgSectorExt_core
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL
open BookProof.QgOuterFockFullFL



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open Filter Topology

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.QgOuterFockFullFL.qgSectorExt_core (n : ℕ) (p : polyGaussCore (d := n * 84))
    (h : (p : L2d (n * 84)) ∈ (harmFried (n * 84)).dom) :
    qgSectorExt n ⟨(p : L2d (n * 84)), h⟩ = qgSectorHam n p := by sorry
