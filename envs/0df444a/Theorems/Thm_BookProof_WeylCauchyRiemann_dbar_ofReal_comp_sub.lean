-- Prove2me | Theorems.Thm_BookProof_WeylCauchyRiemann_dbar_ofReal_comp_sub
-- name    : BookProof.WeylCauchyRiemann.dbar_ofReal_comp_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:13:39.879329+00:00
-- url     : https://prove2.me/theorems/68075260-f7e7-4980-b9f1-f3e5a92ac181
-- title:
--   `BookProof.WeylCauchyRiemann.dbar_ofReal_comp_sub` {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (z w : ℂ) : dbar (fun v => ((χ (z - v) : ℝ) : ℂ)) w = -dbarR χ (z - w)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylCauchyRiemann`.
--
--   `BookProof.WeylCauchyRiemann.dbar_ofReal_comp_sub` {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (z w : ℂ) : dbar (fun v => ((χ (z - v) : ℝ) : ℂ)) w = -dbarR χ (z - w)
--
--   Formalization note: Lean 4 identifier `BookProof.WeylCauchyRiemann.dbar_ofReal_comp_sub`.

-- Generated from ChapterWeylCauchyRiemann.lean — theorem BookProof.WeylCauchyRiemann.dbar_ofReal_comp_sub
import Definitions.Def_ChapterRadialMollifier
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
open BookProof.WeylCauchyRiemann



open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

theorem BookProof.WeylCauchyRiemann.dbar_ofReal_comp_sub {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (z w : ℂ) :
    dbar (fun v => ((χ (z - v) : ℝ) : ℂ)) w = -dbarR χ (z - w) := by sorry
