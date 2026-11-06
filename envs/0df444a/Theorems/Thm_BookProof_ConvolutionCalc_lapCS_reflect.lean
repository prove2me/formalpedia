-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_lapCS_reflect
-- name    : BookProof.ConvolutionCalc.lapCS_reflect
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:12:20.015362+00:00
-- url     : https://prove2.me/theorems/c58bc159-cb5f-45da-9937-0159e7a7d17f
-- title:
--   `BookProof.ConvolutionCalc.lapCS_reflect` {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : Vd d) (S : Finset (Fin d)) (y : Vd d) : lapCS S (fun y => g (x - y)) y = l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.lapCS_reflect` {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : Vd d) (S : Finset (Fin d)) (y : Vd d) : lapCS S (fun y => g (x - y)) y = lapCS S g (x - y)
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.lapCS_reflect`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.lapCS_reflect
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

theorem BookProof.ConvolutionCalc.lapCS_reflect {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : Vd d)
    (S : Finset (Fin d)) (y : Vd d) :
    lapCS S (fun y => g (x - y)) y = lapCS S g (x - y) := by sorry
