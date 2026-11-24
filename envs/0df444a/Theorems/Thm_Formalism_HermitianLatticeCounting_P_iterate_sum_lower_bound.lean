-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_iterate_sum_lower_bound
-- name    : Formalism.HermitianLatticeCounting.P.iterate_sum_lower_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:57.555829+00:00
-- url     : https://prove2.me/theorems/43b27f83-106b-4c8f-bd66-6b8b9092b399
-- title:
--   P: iterate sum lower bound
-- statement:
--   The P construction uses the iterate sum lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1000-L1012
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1000-L1012

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.iterate_sum_lower_bound {R W ι : Type} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] [Fintype ι]
    (Eop : ι → W → W) (Φ : W → R) (κ : R) (hκ : 0 ≤ κ) (h : ∀ w, κ * Φ w ≤ ∑ i, Φ (Eop i w))
    (q : ℕ) (w : W) : κ ^ q * Φ w ≤ ∑ σ : Fin q → ι, Φ ((List.ofFn σ).foldr Eop w) := by sorry
