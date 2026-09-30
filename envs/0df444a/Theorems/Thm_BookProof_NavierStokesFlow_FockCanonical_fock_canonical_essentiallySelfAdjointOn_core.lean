-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_fock_canonical_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.FockCanonical.fock_canonical_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-09-29T18:18:30.961358+00:00
-- url     : https://prove2.me/theorems/d3a074b4-92e0-41d8-98d4-f1cef7230482
-- title:
--   (hκ : ∀ i, 0 ≤ κ i) : EssentiallySelfAdjointOn (lpFiniteModes (Occ d)) ((lpFiniteModes (Occ d)).subtype.comp (∑ i, ((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i))))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FockCanonical.fock_canonical_essentiallySelfAdjointOn_core` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockCanonical.lean — theorem BookProof.NavierStokesFlow.FockCanonical.fock_canonical_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

theorem BookProof.NavierStokesFlow.FockCanonical.fock_canonical_essentiallySelfAdjointOn_core (hκ : ∀ i, 0 ≤ κ i) :
    EssentiallySelfAdjointOn (lpFiniteModes (Occ d))
      ((lpFiniteModes (Occ d)).subtype.comp
        (∑ i, ((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i)))) := by sorry
