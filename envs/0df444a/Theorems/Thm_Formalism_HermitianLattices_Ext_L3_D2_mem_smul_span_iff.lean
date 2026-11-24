-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_span_iff
-- name    : Formalism.HermitianLattices.Ext.L3.D2.mem_smul_span_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:23.925134+00:00
-- url     : https://prove2.me/theorems/bc4973ae-486b-41ad-bc32-f309f21fa88c
-- title:
--   D2: mem smul span iff
-- statement:
--   The D2 construction uses the mem smul span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L155-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulSpanIff.lean#L155-L176

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
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

theorem Formalism.HermitianLattices.Ext.L3.D2.mem_smul_span_iff {κ : Type} [Fintype κ] (a : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (x : V) :
    x ∈ extP K 𝔭 ^ k • locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) ↔
      ∀ i, a.repr x i ∈ pK K 𝔭 k := by sorry
