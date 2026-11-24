-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfM_bc_pr_incl
-- name    : Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM.bc_pr_incl
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:51:33.332939+00:00
-- url     : https://prove2.me/theorems/4210f6ec-2594-4b11-9ee3-76d6ea31817f
-- title:
--   Pf M: bc pr incl
-- statement:
--   The Pf M construction uses the bc pr incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferenceStableUnderAction.lean#L133-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/DifferenceStableUnderAction.lean#L133-L138

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
open Formalism.HermitianLattices.FiltrationBoundaryCriterion Formalism.FrobeniusOrbits NumberField IsDedekindDomain
open scoped TensorProduct

theorem Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfM.bc_pr_incl {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (k : ℕ)
    (w : HeightOneSpectrum (𝓞 F)) (γ₀ : Matrix.GeneralLinearGroup (Fin k) E) :
    Formalism.UG.bc (Formalism.UG.prV (E := E) w) (Formalism.UG.bc (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀) =
      Formalism.UG.bc (Formalism.UG.inclE (F := F) (w.adicCompletion F)) γ₀ := by sorry
