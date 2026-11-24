-- Prove2me | Theorems.Thm_Formalism_LatticeBaseChangeAlt_linearIndependent_of_isBaseChange_alt
-- name    : Formalism.LatticeBaseChangeAlt.linearIndependent_of_isBaseChange_alt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:33.194869+00:00
-- url     : https://prove2.me/theorems/969f731b-e6c1-46e9-887f-e2342a618e31
-- title:
--   Lattice Base Change Alt: linear Independent of is Base Change alt
-- statement:
--   The Lattice Base Change Alt construction uses the linear Independent of is Base Change alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LinearIndependentOfIsBaseChange.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FilteredPoleLength/LocalDescentLevels/LinearIndependentOfIsBaseChange.lean#L9-L28

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LinearIndependentOfIsBaseChange
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

theorem Formalism.LatticeBaseChangeAlt.linearIndependent_of_isBaseChange_alt {K K' V V₁ ι : Type} [Field K] [Field K'] [Algebra K K']
    [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K' V₁] [Module K V₁]
    [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j) (v : ι → V)
    (hv : LinearIndependent K v) : LinearIndependent K' (fun i => j (v i)) := by sorry
