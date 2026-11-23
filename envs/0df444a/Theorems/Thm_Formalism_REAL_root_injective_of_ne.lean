-- Prove2me | Theorems.Thm_Formalism_REAL_root_injective_of_ne
-- name    : Formalism.REAL.root_injective_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:58.547984+00:00
-- url     : https://prove2.me/theorems/828bff43-ab69-4862-8037-4780db962867
-- title:
--   REAL: root injective of ne
-- statement:
--   The REAL construction uses the root injective of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L213-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L213-L227

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.root_injective_of_ne {a b a' b' : Fin n} (hab : a ≠ b) (h : root a b = root a' b') :
    a = a' ∧ b = b' := by sorry
