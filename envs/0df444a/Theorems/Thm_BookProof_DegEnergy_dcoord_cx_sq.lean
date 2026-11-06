-- Prove2me | Theorems.Thm_BookProof_DegEnergy_dcoord_cx_sq
-- name    : BookProof.DegEnergy.dcoord_cx_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:20:42.968593+00:00
-- url     : https://prove2.me/theorems/824507c2-5ca2-444e-9f21-fda890514958
-- title:
--   `BookProof.DegEnergy.dcoord_cx_sq` {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (j : Fin d) (x : Vd d) : dcoord j (fun y => cx χ y ^ 2) x = 2 * cx χ x * dcoord j (cx
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDegEnergyEstimate`.
--
--   `BookProof.DegEnergy.dcoord_cx_sq` {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (j : Fin d) (x : Vd d) : dcoord j (fun y => cx χ y ^ 2) x = 2 * cx χ x * dcoord j (cx χ) x
--
--   Formalization note: Lean 4 identifier `BookProof.DegEnergy.dcoord_cx_sq`.

-- Generated from ChapterDegEnergyEstimate.lean — theorem BookProof.DegEnergy.dcoord_cx_sq
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterConvolutionCalc
import Mathlib
import Definitions.Def_ChapterDegEnergyEstimate
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFockWeightedSchurEsa
open BookProof.HermiteProductCore
open BookProof.DegEnergy



open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger
open BookProof.ConvolutionCalc

noncomputable section

variable {d : ℕ}

variable (S : Finset (Fin d))

theorem BookProof.DegEnergy.dcoord_cx_sq {χ : Vd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (j : Fin d)
    (x : Vd d) : dcoord j (fun y => cx χ y ^ 2) x = 2 * cx χ x * dcoord j (cx χ) x := by sorry
