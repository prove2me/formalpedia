-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_diag
-- name    : Formalism.GaloisIrreducibility.BorderedIndexCases.bord_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:13.556738+00:00
-- url     : https://prove2.me/theorems/1966bf71-8f3d-4d70-9ac9-135da5281fbe
-- title:
--   Bordered Index Cases: bord diag
-- statement:
--   The Bordered Index Cases construction uses the bord diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L47-L54

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

theorem Formalism.GaloisIrreducibility.BorderedIndexCases.bord_diag {n : ℕ} (d : R) :
    bord (diagonal fun i : Fin (n+1) => if (i : ℕ) = n then d else 1) =
      diagonal fun i : Fin (n+2) => if (i : ℕ) = n + 1 then d else 1 := by sorry
