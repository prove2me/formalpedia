-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_natDegree
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:51:10.991812+00:00
-- url     : https://prove2.me/theorems/69e13fd1-a3fe-4f36-8b46-80edc7c595c3
-- title:
--   Galois Irreducibility: monic Of nat Degree
-- statement:
--   The Galois Irreducibility construction uses the monic Of nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L16-L19

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_natDegree (c : Fin N → K) : (monicOf c).natDegree = N := by sorry
