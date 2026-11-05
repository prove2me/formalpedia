-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_hasCompactSupport_finsetSum
-- name    : BookProof.ConvolutionCalc.hasCompactSupport_finsetSum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:12:46.234375+00:00
-- url     : https://prove2.me/theorems/8e61d315-c0f3-4641-97bb-3a32a683edd9
-- title:
--   `BookProof.ConvolutionCalc.hasCompactSupport_finsetSum` {ι : Type*} (s : Finset ι) {f : ι → Vd d → ℂ} (h : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ s,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.hasCompactSupport_finsetSum` {ι : Type*} (s : Finset ι) {f : ι → Vd d → ℂ} (h : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ s, f i x)
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.hasCompactSupport_finsetSum`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.hasCompactSupport_finsetSum
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Mathlib
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.ConvolutionCalc



open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger

noncomputable section

variable {d : ℕ}

theorem BookProof.ConvolutionCalc.hasCompactSupport_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Vd d → ℂ}
    (h : ∀ i ∈ s, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by sorry
