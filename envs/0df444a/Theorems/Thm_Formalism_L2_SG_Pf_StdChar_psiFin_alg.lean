-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_StdChar_psiFin_alg
-- name    : Formalism.L2.SG.Pf.StdChar.psiFin_alg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:36:15.931646+00:00
-- url     : https://prove2.me/theorems/79273358-5c45-4c49-b333-c091f93d01ad
-- title:
--   Std Char: psi Fin alg
-- statement:
--   The Std Char construction uses the psi Fin alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/StdChar.lean#L154-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/StdChar.lean#L154-L161

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_MeasCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_FundamentalContinuity_AdelicIsomorphismStatement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_StdChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Topology Filter
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StdChar
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem Formalism.L2.SG.Pf.StdChar.psiFin_alg (a : F) :
    psiFin F (algebraMap F (Af F) a) = Complex.exp (-(2 * Real.pi * Complex.I * ((trR F a : ℝ) : ℂ))) := by sorry
