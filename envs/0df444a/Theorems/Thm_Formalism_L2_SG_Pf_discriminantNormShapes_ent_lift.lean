-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_lift
-- name    : Formalism.L2.SG.Pf.discriminantNormShapes.ent_lift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:48.078223+00:00
-- url     : https://prove2.me/theorems/a6ee911c-337f-4e41-9068-e0338b12b0e7
-- title:
--   discriminant Norm Shapes: ent lift
-- statement:
--   The discriminant Norm Shapes construction uses the ent lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/EntOfMapEqZero.lean#L163-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/EntOfMapEqZero.lean#L163-L174

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
variable [Fact (IsFixF K F)]

theorem Formalism.L2.SG.Pf.discriminantNormShapes.ent_lift {𝔭 : Ideal (𝓞 F)} {k : ℕ} (hk : 1 ≤ k)
    {A : Matrix c c (𝓞 K)}
    (hA : ∀ i j, Ideal.Quotient.mk (extP K 𝔭 ^ k) (A i j) ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) :
    Ent (extP K 𝔭) A := by sorry
