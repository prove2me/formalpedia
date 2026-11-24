-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x4_stab_sum_zero
-- name    : Formalism.FourierDecayAlt.P.c2x4_stab_sum_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:38:12.754868+00:00
-- url     : https://prove2.me/theorems/ba177f3d-befc-47bf-b613-259902f0f449
-- title:
--   P: c2x4 stab sum zero
-- statement:
--   The P construction uses the c2x4 stab sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L263-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L263-L319

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
open C2x4

theorem Formalism.FourierDecayAlt.P.c2x4_stab_sum_zero {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (hC : Cond w d) (l u' : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) (hu : u' ∈ C2.UTset m)
    (he : l * C2.monoP w d * u' = C2.monoP w d) : C2.simpleLow l + C2.simpleUp u' = 0 := by sorry
