-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_fibreCountingData_diagQ_eq
-- name    : Formalism.L2.SG.Pf.fibreCountingData.diagQ_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:29.478925+00:00
-- url     : https://prove2.me/theorems/e5e8796f-3ded-4c86-93a3-39f508e296d3
-- title:
--   fibre Counting Data: diag Q eq
-- statement:
--   The fibre Counting Data construction uses the diag Q eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CondZIff.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CondZIff.lean#L76-L78

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMulMemSPOfSub
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CondZIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.fibreCountingData
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} [h𝔭 : 𝔭.IsMaximal] {k : ℕ}
local notation "mk" => Ideal.Quotient.mk (extP K 𝔭 ^ k)
variable {m : ℕ} (a : Fin m → 𝓞 F)
variable {a}

theorem Formalism.L2.SG.Pf.fibreCountingData.diagQ_eq : diagQ K 𝔭 k a = (diagonal fun i => ι (a i)).map mk := by sorry
