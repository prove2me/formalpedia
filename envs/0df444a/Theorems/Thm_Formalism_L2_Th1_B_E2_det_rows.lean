-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_E2_det_rows
-- name    : Formalism.L2.Th1.B.E2.det_rows
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:00:58.861583+00:00
-- url     : https://prove2.me/theorems/a65e8d72-d135-40c2-8c44-40a5309bc338
-- title:
--   E2: det rows
-- statement:
--   The E2 construction uses the det rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffLawWithInverseThree.lean#L195-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/ConstantCoeffLawWithInverseThree.lean#L195-L218

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.B.E2.det_rows {R : Type} [CommRing R] (x L A B e : Fin 3 → R) (c0 a1 a3 : R)
    (h2 : ∀ j, x j ^ 2 * A j = L j ^ 2 * (e j + c0 * x j ^ 2))
    (h3 : ∀ j, x j ^ 3 * B j = L j ^ 3 * (-2 * e j + a1 * x j * e j + a3 * x j ^ 3)) :
    (x 0 * x 1 * x 2) ^ 3 * Matrix.det (Matrix.of fun j => ![L j ^ 3, L j * A j, B j]) =
      2 * (L 0 * L 1 * L 2) ^ 3 *
        Matrix.det (Matrix.of fun j => ![x j ^ 3, x j * e j, -e j]) := by sorry
