-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_indep_baseChange
-- name    : Formalism.LatticeBaseChangeAlt.LatticeIndexBis.indep_baseChange
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:52:07.388344+00:00
-- url     : https://prove2.me/theorems/68ab870e-76c2-4d87-bebf-c793fd9922de
-- title:
--   Lattice Index Bis: indep base Change
-- statement:
--   The Lattice Index Bis construction uses the indep base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L159-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LatticeIndexBis.lean#L159-L179

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.LatticeIndexBis

theorem Formalism.LatticeBaseChangeAlt.LatticeIndexBis.indep_baseChange {K K' V V₁ ι : Type} [Field K] [Field K'] [Algebra K K'] [AddCommGroup V]
    [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁] [IsScalarTower K K' V₁]
    (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j) (a : ι → V) (ha : LinearIndependent K a) :
    LinearIndependent K' (fun i => j (a i)) := by sorry
