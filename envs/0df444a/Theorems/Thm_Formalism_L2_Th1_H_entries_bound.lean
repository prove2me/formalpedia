-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_entries_bound
-- name    : Formalism.L2.Th1.H.entries_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:05.871798+00:00
-- url     : https://prove2.me/theorems/3ba44d8e-92de-5c71-bb08-7d36d9e90230
-- title:
--   H: entries bound
-- statement:
--   The H construction uses the entries bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexNeZeroOfNsmulMem.lean#L140-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexNeZeroOfNsmulMem.lean#L140-L168

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CommensurableK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RatFourSquares
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ScalePairMulMulEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexNeZeroOfNsmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.entries_bound (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    {m : Type*} [Fintype m] [DecidableEq m] (f : (m → ℂ) →ₗ[ℂ] (m → ℂ))
    (hf : ∀ w w', InK d (f (Pi.single w' 1) w)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ stdLat (cmL a b d ha hd lam hlam) m, N • f x ∈ stdLat (cmL a b d ha hd lam hlam) m := by sorry
