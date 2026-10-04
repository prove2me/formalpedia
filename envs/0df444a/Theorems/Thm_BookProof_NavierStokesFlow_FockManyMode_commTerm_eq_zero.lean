-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockManyMode_commTerm_eq_zero
-- name    : BookProof.NavierStokesFlow.FockManyMode.commTerm_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T21:13:06.832988+00:00
-- url     : https://prove2.me/theorems/6b5ac1a5-f62a-45f9-84f2-bd5eb2138481
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) (i i₀ : Fin d) (β : Occ d) (hprod : ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β * ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) ((modeData hκ...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockManyMode.commTerm_eq_zero` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockManyMode.lean — theorem BookProof.NavierStokesFlow.FockManyMode.commTerm_eq_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockManyMode

variable {d : ℕ} {κ : Fin d → ℝ}


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian

theorem BookProof.NavierStokesFlow.FockManyMode.commTerm_eq_zero (hκ : ∀ i, 0 ≤ κ i) (i i₀ : Fin d) (β : Occ d)
    (hprod : ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β
      * ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) ((modeData hκ i).shift β) = 0) :
    2 * (modeData hκ i).step * ((modeData hκ i).amp β
      * ((starRingEnd ℂ) (((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ) β)
        * ((testState κ i₀ : L2I (Occ d)) : Occ d → ℂ)
          ((modeData hκ i).shift β)).re) = 0 := by sorry
