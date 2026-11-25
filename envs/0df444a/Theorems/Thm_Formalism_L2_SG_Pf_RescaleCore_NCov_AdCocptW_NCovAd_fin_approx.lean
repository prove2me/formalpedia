-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RescaleCore_NCov_AdCocptW_NCovAd_fin_approx
-- name    : Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW.NCovAd_fin_approx
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:46.312745+00:00
-- url     : https://prove2.me/theorems/9754102e-786b-4741-a07e-6f9d408857df
-- title:
--   Ad Cocpt W: NCov Ad fin approx
-- statement:
--   The Ad Cocpt W construction uses the NCov Ad fin approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/CompactCovering/NCovAd.lean#L106-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/CompactCovering/NCovAd.lean#L106-L120

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_CompactCovering_NCovAd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Metric
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RescaleCore Formalism.L2.SG.Pf.RescaleCore.NCov
open Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW
variable {F : Type} [Field F] [NumberField F]

theorem Formalism.L2.SG.Pf.RescaleCore.NCov.AdCocptW.NCovAd_fin_approx (a : Af F) : ∃ x : F, a - algebraMap F (Af F) x ∈ Formalism.UG.intAd F := by sorry
