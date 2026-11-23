-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_main
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:40.155364+00:00
-- url     : https://prove2.me/theorems/361c138d-151d-4371-baaf-3635c130bfad
-- title:
--   Bordered Index Cases: main
-- statement:
--   The Bordered Index Cases construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L196-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L196-L234

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Matrix
open Matrix
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R] [IsLocalRing R]

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.main (n : ℕ) : ∀ (A : Matrix (Fin (n+1)) (Fin (n+1)) R),
    n ≤ (A.map (IsLocalRing.residue R)).rank →
    ∃ d : R, Equi A (diagonal fun i : Fin (n+1) => if (i : ℕ) = n then d else 1) := by sorry
