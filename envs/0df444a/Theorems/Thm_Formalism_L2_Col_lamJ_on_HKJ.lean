-- Prove2me | Theorems.Thm_Formalism_L2_Col_lamJ_on_HKJ
-- name    : Formalism.L2.Col.lamJ_on_HKJ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:52:13.648553+00:00
-- url     : https://prove2.me/theorems/119886f0-1bd3-592e-b242-ff7cb2d2e774
-- title:
--   Col: lam J on HKJ
-- statement:
--   The Col construction uses the lam J on HKJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L938-L969
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L938-L969

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_HK_le_uniUT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem Formalism.L2.Col.lamJ_on_HKJ (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n r t j : ℕ) (M : ↥(HKJ κ n r t j)) :
    lamJ ψ χ n r t j (Subgroup.inclusion (HK_le_uniUT n κ r _) M) = lamKJ χ n r t j M := by sorry
