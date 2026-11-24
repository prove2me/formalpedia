-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_map_mk_eq_iff
-- name    : Formalism.HermitianLattices.Ext.L3.HU.map_mk_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:28.553143+00:00
-- url     : https://prove2.me/theorems/62c5f8d7-1e3f-46ce-8ac0-c4f3e76acd5e
-- title:
--   HU: map mk eq iff
-- statement:
--   The HU construction uses the map mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeMapMk.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeMapMk.lean#L27-L35

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable [Fact (IsFixF K F)]

theorem Formalism.HermitianLattices.Ext.L3.HU.map_mk_eq_iff (𝔭 : Ideal (𝓞 F)) (k : ℕ) (M N : Matrix κ κ (𝓞 K)) :
    M.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = N.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ↔
      ∀ i j, (M - N) i j ∈ extP K 𝔭 ^ k := by sorry
