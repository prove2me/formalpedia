-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_mul
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.bord_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:04.228109+00:00
-- url     : https://prove2.me/theorems/97085b1a-e0aa-44d2-8e9a-be6e37620fcd
-- title:
--   Bordered Index Cases: bord mul
-- statement:
--   The Bordered Index Cases construction uses the bord mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L27-L30

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
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.bord_mul {m : ℕ} (M N : Matrix (Fin m) (Fin m) R) : bord M * bord N = bord (M * N) := by sorry
