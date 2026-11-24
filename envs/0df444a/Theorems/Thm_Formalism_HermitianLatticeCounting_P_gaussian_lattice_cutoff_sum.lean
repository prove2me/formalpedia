-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gaussian_lattice_cutoff_sum
-- name    : Formalism.HermitianLatticeCounting.P.gaussian_lattice_cutoff_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:16.154804+00:00
-- url     : https://prove2.me/theorems/0a17d0c6-0c9f-48cc-a70f-efa414b601bd
-- title:
--   P: gaussian lattice cutoff sum
-- statement:
--   The P construction uses the gaussian lattice cutoff sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1156-L1156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L1156-L1156

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
open Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.gaussian_lattice_cutoff_sum : Formalism.HermitianLatticeCounting.ExpansionTerms.GaussianLatticeCutoffSum := by sorry
