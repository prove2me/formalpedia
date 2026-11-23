-- Prove2me | Theorems.Thm_Formalism_L2_Col_eW_ne_zero_rat
-- name    : Formalism.L2.Col.eW_ne_zero_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:07.849253+00:00
-- url     : https://prove2.me/theorems/96d9fbee-5945-417c-9d0f-22e8502ff89b
-- title:
--   Col: e W ne zero rat
-- statement:
--   The Col construction uses the e W ne zero rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L565-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L565-L566

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.Col.eW_ne_zero_rat (w : HeightOneSpectrum (𝓞 K)) : (eW w : ℚ) ≠ 0 := by sorry
