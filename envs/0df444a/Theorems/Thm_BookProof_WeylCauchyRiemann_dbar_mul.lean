-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_dbar_mul
-- name    : BookProof.WeylCauchyRiemann.dbar_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:36:18.229107+00:00
-- url     : https://prove2.me/theorems/c458f6f9-0566-4571-853c-f76503ba4486
-- title:
--   `BookProof.WeylCauchyRiemann.dbar_mul` {a b : ℂ → ℂ} {z : ℂ} (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) : dbar (fun w => a w * b w) z = dbar a z * b z + a z * dbar
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.dbar_mul` {a b : ℂ → ℂ} {z : ℂ} (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) : dbar (fun w => a w * b w) z = dbar a z * b z + a z * dbar b z
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.dbar_mul`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.dbar_mul
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.dbar_mul {a b : ℂ → ℂ} {z : ℂ} (ha : DifferentiableAt ℝ a z)
    (hb : DifferentiableAt ℝ b z) :
    dbar (fun w => a w * b w) z = dbar a z * b z + a z * dbar b z := by sorry
