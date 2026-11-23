-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_locRing_local
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.locRing_local
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:47.786253+00:00
-- url     : https://prove2.me/theorems/cbbce832-e029-4cd1-9f7b-5eddda8324e7
-- title:
--   Loc F: loc Ring local
-- statement:
--   The Loc F construction uses the loc Ring local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L100-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L100-L125

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.LocF.locRing_local {p : Ideal (𝓞 K)} (hp : p.IsPrime) :
    ∀ a ∈ locRing p, ∀ b ∈ locRing p, star a = a → star b = b → ¬ IsUnitIn (locRing p) a →
      ¬ IsUnitIn (locRing p) b → IsUnitIn (locRing p) (a + b + 1) := by sorry
