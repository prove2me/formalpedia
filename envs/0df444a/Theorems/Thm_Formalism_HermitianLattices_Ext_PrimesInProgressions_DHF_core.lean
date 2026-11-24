-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_core
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:26.775323+00:00
-- url     : https://prove2.me/theorems/48890bf0-8a4a-4b20-a24d-9731161e737d
-- title:
--   DHF: core
-- statement:
--   The DHF construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishB.lean#L31-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishB.lean#L31-L173

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB
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
set_option maxHeartbeats 1000000

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.core (c' C : ℝ) (A B : ℕ) (hc'0 : 0 < c') (hc'2 : c' ≤ 1 / 2) (hA1 : 1 ≤ A) (hB1 : 1 ≤ B)
    (hC : 0 < C)
    (hT : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
      (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
      ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c' ^ K ≤ (∑ i, z i ^ k).re)
    (q ε l b c₂ : ℝ) (hq : q = c' / 2 ^ A) (hε : ε = q / 4) (hl : l = -Real.log q)
    (hb : b = 2 * B / ε ^ 2 + 4) (hc₂0 : 0 < c₂) (hc₂ : c₂ ≤ ε ^ 2 / (25 * B * C * (2 * l + 2)))
    (large₂ lam η K0 : ℝ) (hK0 : b + 64 * A * Real.exp (l * b) < K0)
    (hη0 : 0 < η) (hηc : η ≤ q ^ 2 / 200) (hlam0 : 0 < lam) (hlamη : lam / η ≤ Real.exp (-K0))
    (hηL : η * large₂ < c₂ * K0) (hLg0 : 0 < large₂)
    (N : ℕ) (w : Fin N → ℂ) (hw : ∀ i, η ≤ (w i).re) (hi0 : ∃ i, w i = ((η + η : ℝ) : ℂ))
    (hpow : ∀ j : ℕ, 1 ≤ j → (∑ i, 1 / (w i) ^ j).re ≤ 2 * j * lam / η ^ (j + 1) + C * large₂ * 25 ^ j) :
    False := by sorry
