-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_exists_next_unit
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.exists_next_unit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:03.411031+00:00
-- url     : https://prove2.me/theorems/ba95fbce-0f46-4df8-a46f-5d73a07c08eb
-- title:
--   Loc F: exists next unit
-- statement:
--   The Loc F construction uses the exists next unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthUnitFrame.lean#L14-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthUnitFrame.lean#L14-L147

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}

theorem Formalism.HermitianLattices.Ext.L3.LocF.exists_next_unit (hS : IsHermSemilocal S)
    (hloc : ∀ a ∈ S, ∀ b ∈ S, star a = a → star b = b → ¬ IsUnitIn S a → ¬ IsUnitIn S b →
      IsUnitIn S (a + b + 1))
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (hM : IsSelfDualMod S h M)
    {ι : Type*} [DecidableEq ι] (x : ι → V) (s : Finset ι) (hxM : ∀ i ∈ s, x i ∈ M)
    (hxo : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → h (x i) (x j) = 0)
    (hxu : ∀ i ∈ s, IsUnitIn S (h (x i) (x i)))
    (v : V) (hv : v ≠ 0) (hvo : ∀ i ∈ s, h (x i) v = 0) :
    ∃ z ∈ M, IsUnitIn S (h z z) ∧ ∀ i ∈ s, h (x i) z = 0 := by sorry
