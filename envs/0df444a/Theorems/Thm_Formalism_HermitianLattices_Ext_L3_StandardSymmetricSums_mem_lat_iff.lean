-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StandardSymmetricSums_mem_lat_iff
-- name    : Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.mem_lat_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:45.006905+00:00
-- url     : https://prove2.me/theorems/83a34cef-7294-4840-a6ec-f8f94d6ff40f
-- title:
--   Standard Symmetric Sums: mem lat iff
-- statement:
--   The Standard Symmetric Sums construction uses the mem lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FiniteDimensionalOfOrtho.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FiniteDimensionalOfOrtho.lean#L69-L73

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums

theorem Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.mem_lat_iff {n : ℕ} {e : Fin n → V} (x : V) :
    x ∈ Submodule.span (𝓞 K) (Set.range e) ↔
      ∃ c : Fin n → 𝓞 K, ∑ i, algebraMap (𝓞 K) K (c i) • e i = x := by sorry
