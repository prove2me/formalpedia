-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_irreducible_of_galois_conditions
-- name    : Formalism.GaloisIrreducibility.irreducible_of_galois_conditions
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:03.635845+00:00
-- url     : https://prove2.me/theorems/5af47a4f-336b-44ec-b50b-df49f4610586
-- title:
--   Galois Irreducibility: irreducible of galois conditions
-- statement:
--   The Galois Irreducibility construction uses the irreducible of galois conditions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/IrredOf.lean#L12-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/IrredOf.lean#L12-L44

import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_IrredOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset

theorem Formalism.GaloisIrreducibility.irreducible_of_galois_conditions : IrredOf := by sorry
