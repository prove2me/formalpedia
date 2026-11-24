-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_substFr_C_mul
-- name    : Formalism.L2.LamCM.substFr_C_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:01.381887+00:00
-- url     : https://prove2.me/theorems/0d9e5330-c4ce-4f2b-9da1-88e0bedb13e2
-- title:
--   Lam CM: subst Fr C mul
-- statement:
--   The Lam CM construction uses the subst Fr C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/LargeResidueExtensionLemma.lean#L46-L49

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
variable {B : Type} {m : B → ℕ}

theorem Formalism.L2.LamCM.substFr_C_mul {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) (a : R)
    (P : MvPolynomial (FrVar m) R) : substFr U (C a * P) = C a * substFr U P := by sorry
