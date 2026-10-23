-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_bigState_symbol_ge
-- name    : BookProof.NavierStokesFlow.FockLagrangian.bigState_symbol_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-22T17:00:43.426739+00:00
-- url     : https://prove2.me/theorems/1741e879-f75f-4b1b-bde1-188372d8c378
-- title:
--   `BookProof.NavierStokesFlow.FockLagrangian.bigState_symbol_ge` {K : ℝ} (hK : 1 ≤ K) : ∀ᵐ x ∂fockR, ((bigState K : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ) x ≠ 0 → K ≤...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockParcels`.
--
--   `BookProof.NavierStokesFlow.FockLagrangian.bigState_symbol_ge` {K : ℝ} (hK : 1 ≤ K) : ∀ᵐ x ∂fockR, ((bigState K : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ) x ≠ 0 → K ≤ |momFock.total x| := by filter_upwards [bigState_coeFn K] with x hx hne rw [hx] at hne have hmem : x ∈ bigSet K
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockLagrangian.bigState_symbol_ge`.

-- Generated from ChapterNavierStokesFockParcels.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.bigState_symbol_ge
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockLagrangian.bigState_symbol_ge {K : ℝ} (hK : 1 ≤ K) :
    ∀ᵐ x ∂fockR, ((bigState K : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ) x ≠ 0
        → K ≤ |momFock.total x| := by sorry
