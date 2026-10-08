-- Prove2me | Theorems.Thm_BookProof_QuantumGravity3DGauge_qg3DElliptic_hashimoto_selects
-- name    : BookProof.QuantumGravity3DGauge.qg3DElliptic_hashimoto_selects
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T18:57:38.101361+00:00
-- url     : https://prove2.me/theorems/57713d19-73c0-4975-8e0e-7653d267058b
-- title:
--   The Lean 4 theorem `qg3DElliptic_hashimoto_selects` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qg3DElliptic_hashimoto_selects` in the `ChapterQuantumGravity3DGauge` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuantumGravity3DGauge.lean

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qg3DElliptic_hashimoto_selects
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

variable {d : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {D : Submodule ℂ (L2d 84)}



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem BookProof.QuantumGravity3DGauge.qg3DElliptic_hashimoto_selects (e : ℕ ≃ (Fin 84 →₀ ℕ)) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ (L2d 84)) (A : Dom →ₗ[ℂ] L2d 84) (R : L2d 84 →L[ℂ] L2d 84),
      IsPositiveSelfAdjointExtension (qg3DEllipticHamiltonian (coreRepBasis e)) A ∧
        IsShiftInvert A γ R ∧ IsSelfAdjoint R ∧
        (∀ u : L2d 84, Filter.Tendsto (fun k : ℕ => galerkinCompression R (coreBasis e) k u)
          Filter.atTop (nhds (R u))) ∧
        (∀ (Dom' : Submodule ℂ (L2d 84)) (A' : Dom' →ₗ[ℂ] L2d 84),
          IsShiftInvert A' γ R → Dom' = Dom) := by sorry
