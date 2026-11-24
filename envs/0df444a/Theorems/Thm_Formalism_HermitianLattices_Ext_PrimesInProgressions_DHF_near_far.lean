-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_near_far
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.near_far
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:29.401913+00:00
-- url     : https://prove2.me/theorems/103850c4-2a2b-4e87-90d3-3b01b8808ccb
-- title:
--   DHF: near far
-- statement:
--   The DHF construction uses the near far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishA.lean#L9-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishA.lean#L9-L119

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.near_far (c : ℝ) (A B : ℕ) (hc : 0 < c)
    (hT : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
      (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
      ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c ^ K ≤ (∑ i, z i ^ k).re)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (N : ℕ) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re) (hi : ∃ i, 1 / 2 ≤ ‖u i‖)
    (K : ℕ) (hK2 : 2 ≤ K) (hKB : (B : ℝ) * (∑ i, (u i).re) ≤ ε ^ 2 * K) :
    ∃ j : ℕ, K ≤ j ∧ j ≤ A * K ∧
      c ^ K * (1 / 2) ^ j ≤ (∑ i, u i ^ j).re + ε ^ (j - 2) * ∑ i, (u i).re := by sorry
