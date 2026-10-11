-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_hasCompactSupport_comp_realProd
-- name    : BookProof.WeylCauchyRiemann.hasCompactSupport_comp_realProd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:33:58.703366+00:00
-- url     : https://prove2.me/theorems/4ad846e6-e9d8-4788-a937-e80cc7684ba2
-- title:
--   `BookProof.WeylCauchyRiemann.hasCompactSupport_comp_realProd` {F : ℂ → ℂ} (hF : HasCompactSupport F) : HasCompactSupport (fun p : ℝ × ℝ => F ((p.1 : ℂ) + p.2 * Complex.I))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.hasCompactSupport_comp_realProd` {F : ℂ → ℂ} (hF : HasCompactSupport F) : HasCompactSupport (fun p : ℝ × ℝ => F ((p.1 : ℂ) + p.2 * Complex.I))
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.hasCompactSupport_comp_realProd`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.hasCompactSupport_comp_realProd
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.hasCompactSupport_comp_realProd {F : ℂ → ℂ} (hF : HasCompactSupport F) :
    HasCompactSupport (fun p : ℝ × ℝ => F ((p.1 : ℂ) + p.2 * Complex.I)) := by sorry
