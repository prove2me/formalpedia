-- Prove2me | Theorems.Thm_Formalism_GM_gaussR_mul_le
-- name    : Formalism.GM.gaussR_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:40.035331+00:00
-- url     : https://prove2.me/theorems/e1bdb36c-6db0-4860-a793-c54dfec630ca
-- title:
--   GM: gauss R mul le
-- statement:
--   The GM construction uses the gauss R mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L46-L65

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
variable {K : Type} [NormedField K]
variable [IsUltrametricDist K]

theorem Formalism.GM.gaussR_mul_le (ρ : NNReal) (P Q : K[X]) :
    gaussR ρ (P * Q) ≤ gaussR ρ P * gaussR ρ Q := by sorry
