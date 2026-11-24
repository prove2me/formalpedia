-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_lOneNorm_eq_sum
-- name    : Formalism.HermitianLatticeCounting.P.lOneNorm_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:04.057084+00:00
-- url     : https://prove2.me/theorems/ecdadeb6-da9e-420a-817d-2a317f92c54a
-- title:
--   P: l One Norm eq sum
-- statement:
--   The P construction uses the l One Norm eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1055-L1057
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1055-L1057

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

theorem Formalism.HermitianLatticeCounting.P.lOneNorm_eq_sum {P : Type} (a : P →₀ ℂ) (s : Finset P) (hs : a.support ⊆ s) :
    lOneNorm a = ∑ i ∈ s, ‖a i‖ := by sorry
