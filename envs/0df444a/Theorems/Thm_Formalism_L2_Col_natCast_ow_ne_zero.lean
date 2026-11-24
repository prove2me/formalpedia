-- Prove2me | Theorems.Thm_Formalism_L2_Col_natCast_ow_ne_zero
-- name    : Formalism.L2.Col.natCast_ow_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:29.798447+00:00
-- url     : https://prove2.me/theorems/c4d4e027-b14f-4afa-96de-d23fe6e22f2e
-- title:
--   Col: nat Cast ow ne zero
-- statement:
--   The Col construction uses the nat Cast ow ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L294-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L294-L298

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

theorem Formalism.L2.Col.natCast_ow_ne_zero (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) : (n : Ow w) ≠ 0 := by sorry
