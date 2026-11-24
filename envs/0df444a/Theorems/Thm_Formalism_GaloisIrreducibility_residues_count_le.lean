-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_residues_count_le
-- name    : Formalism.GaloisIrreducibility.residues_count_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:33.0666+00:00
-- url     : https://prove2.me/theorems/fbac4ebe-b118-468a-aec5-b7a3e6a915d6
-- title:
--   Galois Irreducibility: residues count le
-- statement:
--   The Galois Irreducibility construction uses the residues count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/ResiduesLe.lean#L79-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/ResiduesLe.lean#L79-L97

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe
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

theorem Formalism.GaloisIrreducibility.residues_count_le : ResiduesLe := by sorry
