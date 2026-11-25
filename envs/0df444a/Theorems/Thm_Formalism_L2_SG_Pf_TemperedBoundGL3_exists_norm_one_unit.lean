-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_TemperedBoundGL3_exists_norm_one_unit
-- name    : Formalism.L2.SG.Pf.TemperedBoundGL3.exists_norm_one_unit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:40:57.083032+00:00
-- url     : https://prove2.me/theorems/23e6c630-1488-50c6-a005-7d4b6e21583a
-- title:
--   Tempered Bound GL3: exists norm one unit
-- statement:
--   The Tempered Bound GL3 construction uses the exists norm one unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DivMemLocRingOfVFEq.lean#L82-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DivMemLocRingOfVFEq.lean#L82-L100

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsHermSemilocalLocRing
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOfNormRepCountNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DivMemLocRingOfVFEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.TemperedBoundGL3
open Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
include hK hF

theorem Formalism.L2.SG.Pf.TemperedBoundGL3.exists_norm_one_unit {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {μ : K} (hμ : μ ≠ 0)
    (hN : star μ * μ ∈ WA.locRing P) (hN' : (star μ * μ)⁻¹ ∈ WA.locRing P) :
    ∃ b : K, star b * b = 1 ∧ b * μ⁻¹ ∈ WA.locRing P ∧ μ * b⁻¹ ∈ WA.locRing P := by sorry
