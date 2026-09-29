-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_sum
-- name    : BookProof.NavierStokesFlow.DifferentialL2.Intertwined.sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:22:00.120544+00:00
-- url     : https://prove2.me/theorems/5ee96aeb-0692-448c-bb16-ca595525be81
-- title:
--   The Lean 4 theorem `sum` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sum` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.Intertwined.sum
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

theorem BookProof.NavierStokesFlow.DifferentialL2.Intertwined.sum {ι : Type*} (s : Finset ι)
    {T : ι → lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel}
    {T' : ι → (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3))}
    (h : ∀ i ∈ s, Intertwined (T i) (T' i)) :
    Intertwined (∑ i ∈ s, T i) (∑ i ∈ s, T' i) := by sorry
