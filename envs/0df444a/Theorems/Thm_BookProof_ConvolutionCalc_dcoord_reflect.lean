-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_dcoord_reflect
-- name    : BookProof.ConvolutionCalc.dcoord_reflect
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:12:11.147623+00:00
-- url     : https://prove2.me/theorems/aae0c537-273e-44ef-9338-0970019b523f
-- title:
--   `BookProof.ConvolutionCalc.dcoord_reflect` {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : Vd d) (j : Fin d) : dcoord j (fun y => g (x - y)) = fun y => -(dcoord j g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.dcoord_reflect` {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : Vd d) (j : Fin d) : dcoord j (fun y => g (x - y)) = fun y => -(dcoord j g (x - y))
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.dcoord_reflect`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.dcoord_reflect
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

theorem BookProof.ConvolutionCalc.dcoord_reflect {g : Vd d → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (x : Vd d)
    (j : Fin d) : dcoord j (fun y => g (x - y)) = fun y => -(dcoord j g (x - y)) := by sorry
