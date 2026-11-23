-- Prove2me | Theorems.Thm_Formalism_L2_Col_scalW_eq_locScal
-- name    : Formalism.L2.Col.scalW_eq_locScal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:33.161011+00:00
-- url     : https://prove2.me/theorems/e660c4d0-b164-402c-ac8e-31351db6fd66
-- title:
--   Col: scal W eq loc Scal
-- statement:
--   The Col construction uses the scal W eq loc Scal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L184-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L184-L188

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

theorem Formalism.L2.Col.scalW_eq_locScal (w : HeightOneSpectrum (𝓞 K)) (c : K) (L : Submodule (𝓞 K) V) :
    scalW w c L = @Formalism.LFunctionChainParameters.slopeLatticeData.locScal K V _ _ _ _ _ (plEquiv K w) (owModule w V) c L := by sorry
