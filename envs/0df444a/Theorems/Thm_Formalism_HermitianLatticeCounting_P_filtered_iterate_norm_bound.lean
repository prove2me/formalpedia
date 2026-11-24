-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_filtered_iterate_norm_bound
-- name    : Formalism.HermitianLatticeCounting.P.filtered_iterate_norm_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:07.280775+00:00
-- url     : https://prove2.me/theorems/3bb4fbf6-4e7d-46b7-96e3-dbcf6a4e1c52
-- title:
--   P: filtered iterate norm bound
-- statement:
--   The P construction uses the filtered iterate norm bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1023-L1040
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1023-L1040

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

theorem Formalism.HermitianLatticeCounting.P.filtered_iterate_norm_bound {R W ι : Type} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] [Fintype ι]
    (Eop : ι → W → W) (Nw : W → R) (Fil : ℕ → Set W) (c : ℕ → R) (hc : ∀ j, 0 ≤ c j)
    (hF : ∀ i j w, w ∈ Fil j → Eop i w ∈ Fil (j + 2))
    (hN : ∀ j w, w ∈ Fil j → ∑ i, Nw (Eop i w) ≤ c j * Nw w) (q j : ℕ) (w : W) (hw : w ∈ Fil j) :
    ∑ σ : Fin q → ι, Nw ((List.ofFn σ).foldr Eop w) ≤ (∏ i ∈ range q, c (j + 2 * i)) * Nw w := by sorry
