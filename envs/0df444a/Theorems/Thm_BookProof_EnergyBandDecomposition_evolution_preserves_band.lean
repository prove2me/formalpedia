-- Prove2me | Theorems.Thm_BookProof_EnergyBandDecomposition_evolution_preserves_band
-- name    : BookProof.EnergyBandDecomposition.evolution_preserves_band
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:46:00.684309+00:00
-- url     : https://prove2.me/theorems/02e9a13f-5f2a-499a-912b-86e9cad9b053
-- title:
--   `BookProof.EnergyBandDecomposition.evolution_preserves_band` (t : ℝ) (f : X → ℂ) (k : ℤ) : Function.support (fun x => Complex.exp (-(Complex.I * (t * E x))) * bandPart E ε k f x) ⊆
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEnergyBandDecomposition`.
--
--   `BookProof.EnergyBandDecomposition.evolution_preserves_band` (t : ℝ) (f : X → ℂ) (k : ℤ) : Function.support (fun x => Complex.exp (-(Complex.I * (t * E x))) * bandPart E ε k f x) ⊆ band E ε k
--
--   Formalization note: Lean 4 identifier `BookProof.EnergyBandDecomposition.evolution_preserves_band`.

-- Generated from ChapterEnergyBandDecomposition.lean — theorem BookProof.EnergyBandDecomposition.evolution_preserves_band
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition



open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

theorem BookProof.EnergyBandDecomposition.evolution_preserves_band (t : ℝ) (f : X → ℂ) (k : ℤ) :
    Function.support (fun x => Complex.exp (-(Complex.I * (t * E x))) * bandPart E ε k f x)
      ⊆ band E ε k := by sorry
