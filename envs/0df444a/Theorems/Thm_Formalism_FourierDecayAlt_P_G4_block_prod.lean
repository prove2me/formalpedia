-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_block_prod
-- name    : Formalism.FourierDecayAlt.P.G4.block_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:10.617809+00:00
-- url     : https://prove2.me/theorems/256ca1a5-b076-4310-8c4c-85cfbc0939dc
-- title:
--   G4: block prod
-- statement:
--   The G4 construction uses the block prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L340-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L340-L346

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4

theorem Formalism.FourierDecayAlt.P.G4.block_prod {n : ℕ} (t c : ℂ) (l' u' : Matrix (Fin n) (Fin n) ℂ) (α β : Fin n → ℂ) :
    blk l' 0 α 1 * ptBlock n t c * blk u' β 0 1 =
      blk (l' * (t • wMat n) * u') ((l' * (t • wMat n)) *ᵥ β) (α ᵥ* ((t • wMat n) * u'))
        ((α ᵥ* (t • wMat n)) ⬝ᵥ β + c) := by sorry
