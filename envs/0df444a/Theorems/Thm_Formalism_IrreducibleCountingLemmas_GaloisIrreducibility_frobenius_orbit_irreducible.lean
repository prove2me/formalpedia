-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_frobenius_orbit_irreducible
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.frobenius_orbit_irreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:41.970248+00:00
-- url     : https://prove2.me/theorems/4923baf3-32e8-4245-925f-a2587b6c570d
-- title:
--   Galois Irreducibility: frobenius orbit irreducible
-- statement:
--   The Galois Irreducibility construction uses the frobenius orbit irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRFrobOrbitIrred.lean#L9-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRFrobOrbitIrred.lean#L9-L70

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
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
open Formalism.GaloisIrreducibility (IsOrbit)

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.frobenius_orbit_irreducible : FrobOrbitIrred := by sorry
