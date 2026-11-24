-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_NO_algF_mem_pK
-- name    : Formalism.HermitianLattices.Ext.L3.D2.NO.algF_mem_pK
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:45:14.681799+00:00
-- url     : https://prove2.me/theorems/c6753f32-b26a-488a-9e4b-538374593036
-- title:
--   NO: alg F mem p K
-- statement:
--   The NO construction uses the alg F mem p K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulEqUnifPow.lean#L39-L46

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.NO

theorem Formalism.HermitianLattices.Ext.L3.D2.NO.algF_mem_pK {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {s : 𝓞 F} (hs : s ∈ 𝔭 ^ k) :
    algebraMap F K (s : F) ∈ pK K 𝔭 k := by sorry
