-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfM_coord
-- name    : Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM.coord
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:53:51.569617+00:00
-- url     : https://prove2.me/theorems/7eab3965-eec3-48ac-9d3f-f2919d167045
-- title:
--   Pf M: coord
-- statement:
--   The Pf M construction uses the coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferenceStableUnderAction.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferenceStableUnderAction.lean#L111-L115

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_OrbitPointsDistinct
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_BehrendSets_TranslateMean
import Definitions.Def_Formalism_BehrendSets_FinalE
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.FiltrationBoundaryCriterion
open Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits

theorem Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM.coord {e : ℕ} (ι : HGrp e ≃* Multiplicative (ZMod (2 ^ e))) (φ τ : GG e)
    (hφ : φ.1 = c0 ∨ φ.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (i : ℤ) :
    Multiplicative.toAdd (ι (placeOf (φ ^ i * τ)).2) =
      Multiplicative.toAdd (ι τ.2) + i • Multiplicative.toAdd (ι φ.2) := by sorry
