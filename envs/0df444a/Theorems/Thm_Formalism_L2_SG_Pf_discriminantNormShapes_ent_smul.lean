-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_smul
-- name    : Formalism.L2.SG.Pf.discriminantNormShapes.ent_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:12.297883+00:00
-- url     : https://prove2.me/theorems/de29b8ff-6a9e-4daa-b40f-6c797b357980
-- title:
--   discriminant Norm Shapes: ent smul
-- statement:
--   The discriminant Norm Shapes construction uses the ent smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/EntOfMapEqZero.lean#L40-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/EntOfMapEqZero.lean#L40-L40

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

theorem Formalism.L2.SG.Pf.discriminantNormShapes.ent_smul {J : Ideal (𝓞 K)} (a : 𝓞 K) {A : Matrix c c (𝓞 K)} (hA : Ent J A) : Ent J (a • A) := by sorry
