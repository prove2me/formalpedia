-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_isSubSum_of_subset
-- name    : Formalism.GaloisIrreducibility.isSubSum_of_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:07.487667+00:00
-- url     : https://prove2.me/theorems/59e8b683-2527-400a-ba2e-1ef8076ad83e
-- title:
--   Galois Irreducibility: is Sub Sum of subset
-- statement:
--   The Galois Irreducibility construction uses the is Sub Sum of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/IrredOf.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/IrredOf.lean#L7-L10

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

theorem Formalism.GaloisIrreducibility.isSubSum_of_subset {ι : Type} (f : ι → ℕ) (I J : Finset ι) (hJ : J ⊆ I) :
    IsSubSum (I.val.map f) (∑ i ∈ J, f i) := by sorry
