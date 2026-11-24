-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_irred
-- name    : Formalism.GaloisIrreducibility.irred
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:08.150951+00:00
-- url     : https://prove2.me/theorems/562f9cc1-c35f-4be9-8fa2-bea1d5087f96
-- title:
--   Galois Irreducibility: irred
-- statement:
--   The Galois Irreducibility construction uses the irred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/NoSolvableTransitive.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/NoSolvableTransitive.lean#L20-L20

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

theorem Formalism.GaloisIrreducibility.irred : Irred := by sorry
