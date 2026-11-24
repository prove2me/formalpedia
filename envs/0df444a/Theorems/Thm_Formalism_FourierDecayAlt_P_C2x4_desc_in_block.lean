-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_desc_in_block
-- name    : Formalism.FourierDecayAlt.P.C2x4.desc_in_block
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:13:16.421917+00:00
-- url     : https://prove2.me/theorems/b2075aaf-185f-4bb7-ba47-2d56a58f5fa1
-- title:
--   C2x4: desc in block
-- statement:
--   The C2x4 construction uses the desc in block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L127-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L127-L137

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x4.desc_in_block (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a b : Fin m)
    (hab : blk w a = blk w b) (j : Fin m) (hj1 : a ≤ j) (hj2 : j.val + 1 ≤ b.val) :
    ∃ h : j.val + 1 < m, w ⟨j.val + 1, h⟩ < w j := by sorry
