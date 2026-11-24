-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_vF_lt_of_notMem
-- name    : Formalism.HermitianLattices.Ext.L3.MeanC.vF_lt_of_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:27.254792+00:00
-- url     : https://prove2.me/theorems/02fcf728-def7-440e-ae4b-14a52068e219
-- title:
--   Mean C: v F lt of not Mem
-- statement:
--   The Mean C construction uses the v F lt of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoMeanAlphaN.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoMeanAlphaN.lean#L28-L38

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.MeanC

theorem Formalism.HermitianLattices.Ext.L3.MeanC.vF_lt_of_notMem {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {j : ℕ} (h : n ∉ 𝔭 ^ j) : vF 𝔭 n < j := by sorry
