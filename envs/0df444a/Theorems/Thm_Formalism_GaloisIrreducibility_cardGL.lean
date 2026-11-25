-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_cardGL
-- name    : Formalism.GaloisIrreducibility.cardGL
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:16.087172+00:00
-- url     : https://prove2.me/theorems/1ce3f0ad-26e9-4eb0-8ad5-01a9b9de3728
-- title:
--   Galois Irreducibility: card GL
-- statement:
--   The Galois Irreducibility construction uses the card GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/NoSolvableTransitive.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/NoSolvableTransitive.lean#L25-L33

import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_RestrictRoots
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_LemmaAOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_IrredOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_FewLargeParts
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_BlockBoundOfOrbits
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PowerPCycle
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_AltNotSolvable
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_NoSolvableOf
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PrimitiveOfPCycle
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility

theorem Formalism.GaloisIrreducibility.cardGL : CardGL := by sorry
