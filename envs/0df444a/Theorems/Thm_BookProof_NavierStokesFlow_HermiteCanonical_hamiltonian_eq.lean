-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_HermiteCanonical_hamiltonian_eq
-- name    : BookProof.NavierStokesFlow.HermiteCanonical.hamiltonian_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:24:05.705358+00:00
-- url     : https://prove2.me/theorems/67b29847-b1bd-4288-bf13-12805b0eafaf
-- title:
--   (hκ : 0 ≤ κ) : (lpFiniteModes ℕ).subtype.comp (((1 : ℂ) / 2) • ((mom κ).comp (drift κ) + (drift κ).comp (mom κ))) = (nsH κ hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ)))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.HermiteCanonical.hamiltonian_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.hamiltonian_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}

theorem BookProof.NavierStokesFlow.HermiteCanonical.hamiltonian_eq (hκ : 0 ≤ κ) :
    (lpFiniteModes ℕ).subtype.comp
        (((1 : ℂ) / 2) • ((mom κ).comp (drift κ) + (drift κ).comp (mom κ)))
      = (nsH κ hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ))) := by sorry
