-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_quad_eq_zero
-- name    : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.quad_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:53.287325+00:00
-- url     : https://prove2.me/theorems/ef135dee-ab45-4097-a2d1-2fba0095a1fe
-- title:
--   Hermitian Sublattices: quad eq zero
-- statement:
--   The Hermitian Sublattices construction uses the quad eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L236-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L236-L245

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]

theorem Formalism.HermitianLattices.Ext.L3.HermitianSublattices.quad_eq_zero {𝔟 : Ideal A} (h𝔟s : ∀ a ∈ 𝔟, star a ∈ 𝔟) (h𝔟2 : ∀ a ∈ 𝔟, ∀ b ∈ 𝔟, a * b = 0)
    (H : Matrix m m A) {Y : Matrix m r A} (hY : Y ∈ entSub m r 𝔟) : Yᴴ * H * Y = 0 := by sorry
