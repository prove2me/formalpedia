-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_exists_shifts
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.exists_shifts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:47:12.596322+00:00
-- url     : https://prove2.me/theorems/ccb5c8a2-9fca-4f9f-a29e-c505df140cec
-- title:
--   Box Sum: exists shifts
-- statement:
--   The Box Sum construction uses the exists shifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumCoset.lean#L62-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumCoset.lean#L62-L100

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.exists_shifts {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    ∃ (y y' : 𝓞 F) (R : ℝ), (∀ w, 0 ≤ rEmb w y ∧ rEmb w y ≤ R) ∧ (∀ w, 0 ≤ rEmb w y' ∧ rEmb w y' ≤ R) ∧
      (∀ n, n - x₀ ∈ I → n + y ∈ I) ∧ ∀ n, n ∈ I → n + y' - x₀ ∈ I := by sorry
