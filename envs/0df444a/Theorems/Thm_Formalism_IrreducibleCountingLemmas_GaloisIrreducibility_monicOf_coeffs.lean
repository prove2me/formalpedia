-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_coeffs
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_coeffs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:44.692957+00:00
-- url     : https://prove2.me/theorems/6c91c886-9c25-46be-a082-8cab0ad284ed
-- title:
--   Galois Irreducibility: monic Of coeffs
-- statement:
--   The Galois Irreducibility construction uses the monic Of coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRIrredCountUpper.lean#L37-L41

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf_coeffs {p : K[X]} (hp : p.Monic) (hN : p.natDegree = N) :
    monicOf (fun i : Fin N => p.coeff i) = p := by sorry
