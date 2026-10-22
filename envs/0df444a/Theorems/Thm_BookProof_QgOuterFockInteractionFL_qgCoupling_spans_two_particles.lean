-- Prove2me | Theorems.Thm_BookProof_QgOuterFockInteractionFL_qgCoupling_spans_two_particles
-- name    : BookProof.QgOuterFockInteractionFL.qgCoupling_spans_two_particles
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T12:26:27.229421+00:00
-- url     : https://prove2.me/theorems/58d9fa16-2427-41bd-8ee1-2473d2b54b40
-- title:
--   `BookProof.QgOuterFockInteractionFL.qgCoupling_spans_two_particles` (lam : ℝ) {n : ℕ} (p : Fin n) (hp : nextPart p ≠ p) {m : Fin 64} (hm : torsionMu m ≠ torsionNu m) : qgIntVec lam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockInteractionFL`.
--
--   `BookProof.QgOuterFockInteractionFL.qgCoupling_spans_two_particles` (lam : ℝ) {n : ℕ} (p : Fin n) (hp : nextPart p ≠ p) {m : Fin 64} (hm : torsionMu m ≠ torsionNu m) : qgIntVec lam n (Sum.inr (p, m)) (pcoord p (torsionIdx1 m)) = lam ∧ qgIntVec lam n (Sum.inr (p, m)) (pcoord (nextPart p) (torsionIdx1 m)) = -lam
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockInteractionFL.qgCoupling_spans_two_particles`.

-- Generated from ChapterQgOuterFockInteractionFL.lean — theorem BookProof.QgOuterFockInteractionFL.qgCoupling_spans_two_particles
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.Qg3DGaugeEsa
open BookProof.QgOuterFock
open BookProof.QgOuterFockInteractionFL



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine

noncomputable section

variable (F : QgFamily)

theorem BookProof.QgOuterFockInteractionFL.qgCoupling_spans_two_particles (lam : ℝ) {n : ℕ} (p : Fin n)
    (hp : nextPart p ≠ p) {m : Fin 64} (hm : torsionMu m ≠ torsionNu m) :
    qgIntVec lam n (Sum.inr (p, m)) (pcoord p (torsionIdx1 m)) = lam ∧
      qgIntVec lam n (Sum.inr (p, m)) (pcoord (nextPart p) (torsionIdx1 m)) = -lam := by sorry
