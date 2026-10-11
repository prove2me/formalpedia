-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_dbar_eq_zero_of_notMem_tsupport
-- name    : BookProof.WeylCauchyRiemann.dbar_eq_zero_of_notMem_tsupport
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:35:39.954258+00:00
-- url     : https://prove2.me/theorems/6653e92b-574e-48a2-8f0f-f55d05ea1d82
-- title:
--   `BookProof.WeylCauchyRiemann.dbar_eq_zero_of_notMem_tsupport` {φ : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport φ) : dbar φ z = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.dbar_eq_zero_of_notMem_tsupport` {φ : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport φ) : dbar φ z = 0
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.dbar_eq_zero_of_notMem_tsupport`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.dbar_eq_zero_of_notMem_tsupport
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.dbar_eq_zero_of_notMem_tsupport {φ : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport φ) :
    dbar φ z = 0 := by sorry
