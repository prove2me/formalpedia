-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G6_pow_apply_zero
-- name    : Formalism.FourierDecayAlt.P.G6.pow_apply_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:53.114417+00:00
-- url     : https://prove2.me/theorems/e41fec8e-6443-45c4-a792-2c89be9ca879
-- title:
--   G6: pow apply zero
-- statement:
--   The G6 construction uses the pow apply zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L63-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RemainderNormLeStrictUpper.lean#L63-L79

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G6
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G6.pow_apply_zero {m : ℕ} {X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hX : IsStrictUpper X) :
    ∀ (j : ℕ) (hj : j < m + 1), (X ^ j) 0 ⟨j, hj⟩ =
      ∏ k : Fin j, X ⟨k, by omega⟩ ⟨k + 1, by omega⟩ := by sorry
