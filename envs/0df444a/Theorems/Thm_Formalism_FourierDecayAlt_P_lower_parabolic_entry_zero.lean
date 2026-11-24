-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_lower_parabolic_entry_zero
-- name    : Formalism.FourierDecayAlt.P.lower_parabolic_entry_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:23.72194+00:00
-- url     : https://prove2.me/theorems/73195a92-cf1a-42bc-9b03-7d316d24848a
-- title:
--   P: lower parabolic entry zero
-- statement:
--   The P construction uses the lower parabolic entry zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetSubmatrixUnitriangularEqOne.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetSubmatrixUnitriangularEqOne.lean#L19-L28

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetSubmatrixUnitriangularEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 CardInsertEmbedding DeterminantReindex

theorem Formalism.FourierDecayAlt.P.lower_parabolic_entry_zero {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LPg (C2.monoP w d)) (x y : Fin m) (hxy : x < y) :
    l (w x) (w y) = 0 := by sorry
