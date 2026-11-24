-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_foldr_mem_filtration
-- name    : Formalism.HermitianLatticeCounting.P.foldr_mem_filtration
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:20.125343+00:00
-- url     : https://prove2.me/theorems/d96318d1-9f00-4ad8-81fa-d3a05782e11e
-- title:
--   P: foldr mem filtration
-- statement:
--   The P construction uses the foldr mem filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1014-L1021
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1014-L1021

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

theorem Formalism.HermitianLatticeCounting.P.foldr_mem_filtration {W ι : Type} (Eop : ι → W → W) (Fil : ℕ → Set W)
    (hF : ∀ i j w, w ∈ Fil j → Eop i w ∈ Fil (j + 2)) (j : ℕ) (w : W) (hw : w ∈ Fil j) (l : List ι) :
    l.foldr Eop w ∈ Fil (j + 2 * l.length) := by sorry
