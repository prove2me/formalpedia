-- Prove2me | Theorems.Thm_BornVolume_born_vector_uniform_of_invariant
-- name    : BornVolume.born_vector_uniform_of_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:11.690624+00:00
-- url     : https://prove2.me/theorems/1ae949c9-9b9e-4aeb-b924-773dbc5467b3
-- title:
--   Born Volume: born vector uniform of invariant
-- statement:
--   **Born weights are Fubini–Study volumes: the Born vector of a random state is uniform.**
--   For a pure state chosen with any unitarily invariant probability measure `μ` on `ℂℙᴹ`, the Born
--   probability vector is uniformly distributed on the probability simplex: in free coordinates its
--   law is `M!` times Lebesgue measure on the open simplex `{t | 0 < tₖ, ∑ tₖ < 1}`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L106-L113
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean#L106-L113

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}

theorem BornVolume.born_vector_uniform_of_invariant (μ : Measure (CPN (M + 1))) [IsProbabilityMeasure μ]
    (hμ : ∀ U : Matrix.unitaryGroup (Fin (M + 1)) ℂ, Measure.map (fun p => U • p) μ = μ) :
    Measure.map (fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) μ
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by sorry
