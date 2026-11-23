-- Prove2me | Theorems.Thm_Formalism_L2_Col_ow_smul_def
-- name    : Formalism.L2.Col.ow_smul_def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:13.50539+00:00
-- url     : https://prove2.me/theorems/055f1699-4f90-46f7-b5c9-2ed8e64742e7
-- title:
--   Col: ow smul def
-- statement:
--   The Col construction uses the ow smul def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L76-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L76-L76

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
variable (w : HeightOneSpectrum (𝓞 K)) (V : Type) [AddCommGroup V] [Module K V]
variable {V}

theorem Formalism.L2.Col.ow_smul_def (r : Ow w) (x : V) : r • x = algebraMap (Ow w) K r • x := by sorry
