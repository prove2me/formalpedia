-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_sub
-- name    : Formalism.L2.SG.Pf.discriminantNormShapes.ent_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:25.427695+00:00
-- url     : https://prove2.me/theorems/094a1d41-1f30-4023-8ad5-2466db1724ef
-- title:
--   discriminant Norm Shapes: ent sub
-- statement:
--   The discriminant Norm Shapes construction uses the ent sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/EntOfMapEqZero.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/EntOfMapEqZero.lean#L35-L36

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EntOfMapEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]

theorem Formalism.L2.SG.Pf.discriminantNormShapes.ent_sub {J : Ideal (𝓞 K)} {A B : Matrix c c (𝓞 K)} (hA : Ent J A) (hB : Ent J B) :
    Ent J (A - B) := by sorry
