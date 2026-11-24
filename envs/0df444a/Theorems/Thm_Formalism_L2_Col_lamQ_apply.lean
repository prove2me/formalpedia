-- Prove2me | Theorems.Thm_Formalism_L2_Col_lamQ_apply
-- name    : Formalism.L2.Col.lamQ_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:59.115888+00:00
-- url     : https://prove2.me/theorems/da8f8462-0297-43a3-a19a-60480b2d18a8
-- title:
--   Col: lam Q apply
-- statement:
--   The Col construction uses the lam Q apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L619-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean#L619-L622

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
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
variable (κ : Type) [CommRing κ] {K : Type} [Field K]
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}
variable (κ)
variable {κ}

theorem Formalism.L2.Col.lamQ_apply (ξ : κˣ →* Kˣ) (n a b : ℕ) (M : ↥(HQ κ n a b)) :
    lamQ ξ n a b M = ξ (blkDet n κ (coarse a [b]) 1 M) := by sorry
