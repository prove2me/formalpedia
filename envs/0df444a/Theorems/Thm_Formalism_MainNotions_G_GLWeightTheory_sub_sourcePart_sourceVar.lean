-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sub_sourcePart_sourceVar
-- name    : Formalism.MainNotions.G.GLWeightTheory.sub_sourcePart_sourceVar
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:55:20.617328+00:00
-- url     : https://prove2.me/theorems/afae147c-fdad-45f0-9c10-65f522311466
-- title:
--   GLWeight Theory: sub source Part source Var
-- statement:
--   The GLWeight Theory construction uses the sub source Part source Var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionMonomialOfFixed.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionMonomialOfFixed.lean#L51-L58

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionMonomialOfFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)

theorem Formalism.MainNotions.G.GLWeightTheory.sub_sourcePart_sourceVar (l : ι) (hl : l ∈ S) : (m - sourceVariableExponent LL S a b m) (sourceVar LL a b l) = 0 := by sorry
