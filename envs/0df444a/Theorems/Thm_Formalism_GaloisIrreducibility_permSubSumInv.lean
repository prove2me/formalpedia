-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_permSubSumInv
-- name    : Formalism.GaloisIrreducibility.permSubSumInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:45.031595+00:00
-- url     : https://prove2.me/theorems/c4806c18-2a12-448d-a57b-6d9ec3b1ae35
-- title:
--   Galois Irreducibility: perm Sub Sum Inv
-- statement:
--   The Galois Irreducibility construction uses the perm Sub Sum Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/NoSolvableTransitive.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/NoSolvableTransitive.lean#L21-L21

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

theorem Formalism.GaloisIrreducibility.permSubSumInv : PermSubSumInv := by sorry
