-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_kFin_smooth
-- name    : CompanionTheory.D.gk.admitted.kFin_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:32.703134+00:00
-- url     : https://prove2.me/theorems/dfb5e4b9-9286-4268-b6a7-b324c2851b3b
-- title:
--   admitted: k Fin smooth
-- statement:
--   The admitted construction uses the k Fin smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinalAll.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/FinalAll.lean#L12-L15

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Definitions.Def_Formalism_PeriodIntegrals_PhMeasCore
import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinalAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep

theorem CompanionTheory.D.gk.admitted.kFin_smooth (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) (v : H) (hv : IsKFin ε σ v) : SmoothOnH (Jm ε) fun g => σ g v := by sorry
