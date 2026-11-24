-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_sum_relIndex_fibre
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.sum_relIndex_fibre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:26.222896+00:00
-- url     : https://prove2.me/theorems/215a817a-de85-4886-924c-49f26cb18124
-- title:
--   LIOrb: sum rel Index fibre
-- statement:
--   The LIOrb construction uses the sum rel Index fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqOfCover.lean#L107-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexEqOfCover.lean#L107-L163

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
open Subgroup
variable {G : Type*} [Group G]

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.sum_relIndex_fibre {X Y : Type*} [MulAction G X] [MulAction G Y] (π : X → Y)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ x ∈ sX, x ∈ A ∧ π x ∈ sY)
    (hX : ∀ x ∈ A, ∃! t, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ sY, ∀ y' ∈ sY, (∃ g : G, g • y = y') → y = y')
    (hfin : ∀ x ∈ sX, (MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) ≠ 0)
    (w : Y → ℝ) :
    ∑ x ∈ sX, ((MulAction.stabilizer G x).relIndex (MulAction.stabilizer G (π x)) : ℝ) * w (π x) =
      ∑ y ∈ sY, (Nat.card {x // x ∈ A ∧ π x = y} : ℝ) * w y := by sorry
