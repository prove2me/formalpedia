-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_norm_expTerm_le
-- name    : Formalism.L2.Th1.H.norm_expTerm_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:49:10.544193+00:00
-- url     : https://prove2.me/theorems/e92f31fd-fc18-4291-b467-be32b972628a
-- title:
--   H: norm exp Term le
-- statement:
--   The H construction uses the norm exp Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L28-L34

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Formalism.L2.Th1.H.norm_expTerm_le {X : Type*} (c : X → ℂ) (l : X → V →L[ℂ] ℂ) (n : ℕ) (x : X) :
    ‖expTerm c l n x‖ ≤ ‖c x‖ * (‖l x‖ ^ n / (n ! : ℝ)) := by sorry
