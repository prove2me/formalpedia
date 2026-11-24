-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_powForm_diag
-- name    : Formalism.L2.Th1.H.powForm_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:48:46.125803+00:00
-- url     : https://prove2.me/theorems/0a298818-08ad-4fc5-a3bd-3a3cb71747ca
-- title:
--   H: pow Form diag
-- statement:
--   The H construction uses the pow Form diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L16-L17

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

theorem Formalism.L2.Th1.H.powForm_diag (l : V →L[ℂ] ℂ) (n : ℕ) (y : V) : powForm l n (fun _ => y) = l y ^ n := by sorry
