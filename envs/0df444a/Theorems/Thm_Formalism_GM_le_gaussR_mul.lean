-- Prove2me | Theorems.Thm_Formalism_GM_le_gaussR_mul
-- name    : Formalism.GM.le_gaussR_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:58.052166+00:00
-- url     : https://prove2.me/theorems/d6ec3c10-b3d7-4699-8696-7aa874cce1ec
-- title:
--   GM: le gauss R mul
-- statement:
--   The GM construction uses the le gauss R mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L67-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GaussRad.lean#L67-L125

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

theorem Formalism.GM.le_gaussR_mul (ρ : NNReal) (hρ : 0 < ρ) (P Q : K[X]) :
    gaussR ρ P * gaussR ρ Q ≤ gaussR ρ (P * Q) := by sorry
