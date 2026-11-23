-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_sum_inv_card_stab
-- name    : Formalism.HermitianLattices.Ext.L3.sum_inv_card_stab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:55.046262+00:00
-- url     : https://prove2.me/theorems/4cce2be9-ab07-495f-a5c9-534b28ea030e
-- title:
--   L3: sum inv card stab
-- statement:
--   The L3 construction uses the sum inv card stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FiniteRepSetOfOrtho.lean#L10-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FiniteRepSetOfOrtho.lean#L10-L61

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_AutFinite
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
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

theorem Formalism.HermitianLattices.Ext.L3.sum_inv_card_stab {G X : Type*} [Group G] [Finite G] [MulAction G X] (A : Set X)
    [Finite A] (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (T : Finset X) (hTA : ∀ t ∈ T, t ∈ A)
    (hT : ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x) :
    (Nat.card A : ℝ) / (Nat.card G : ℝ) =
      ∑ t ∈ T, ((Nat.card (MulAction.stabilizer G t) : ℕ) : ℝ)⁻¹ := by sorry
