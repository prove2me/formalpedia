-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_cnv_finset_sum
-- name    : BookProof.ConvolutionCalc.cnv_finset_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:13:18.119871+00:00
-- url     : https://prove2.me/theorems/ab419906-70cb-4760-a99b-c81d920c998c
-- title:
--   `BookProof.ConvolutionCalc.cnv_finset_sum` {ι : Type*} (s : Finset ι) {u : Vd d → ℂ} {g : ι → Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hg : ∀ i ∈ s, Continuo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.cnv_finset_sum` {ι : Type*} (s : Finset ι) {u : Vd d → ℂ} {g : ι → Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hg : ∀ i ∈ s, Continuous (g i)) (hgc : ∀ i ∈ s, HasCompactSupport (g i)) (x : Vd d) : cnv u (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, cnv u (g i) x
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.cnv_finset_sum`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.cnv_finset_sum
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Mathlib
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFockWeightedSchurEsa
open BookProof.HermiteProductCore
open BookProof.ConvolutionCalc



open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger

noncomputable section

variable {d : ℕ}

theorem BookProof.ConvolutionCalc.cnv_finset_sum {ι : Type*} (s : Finset ι) {u : Vd d → ℂ} {g : ι → Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d)))
    (hg : ∀ i ∈ s, Continuous (g i)) (hgc : ∀ i ∈ s, HasCompactSupport (g i)) (x : Vd d) :
    cnv u (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, cnv u (g i) x := by sorry
