-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_irreducible
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight_irreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:07:30.544009+00:00
-- url     : https://prove2.me/theorems/f7c128b4-43c8-469b-870b-709bd8dff4c8
-- title:
--   Galois Irreducibility: sq Weight irreducible
-- statement:
--   The Galois Irreducibility construction uses the sq Weight irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L14-L24

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight_irreducible {K : Type} [Field K] [Fintype K] (P : K[X]) (hP : Irreducible P)
    (hm : P.Monic) : sqWeight P = ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹ := by sorry
