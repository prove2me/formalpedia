-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_fixed_nonunit
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.fixed_nonunit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:28.899903+00:00
-- url     : https://prove2.me/theorems/43778301-8ba3-4148-9848-3f2ee2de4711
-- title:
--   Loc F: fixed nonunit
-- statement:
--   The Loc F construction uses the fixed nonunit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L83-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L83-L98

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

theorem Formalism.HermitianLattices.Ext.L3.LocF.fixed_nonunit {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p)
    (hfix : star a = a) (hnu : ¬ IsUnitIn (locRing p) a) :
    ∃ r ∈ p, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s := by sorry
