-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_hermSub
-- name    : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:18.646403+00:00
-- url     : https://prove2.me/theorems/b34dc560-a2c6-45ea-8e56-f027673056fe
-- title:
--   Hermitian Sublattices: mem herm Sub
-- statement:
--   The Hermitian Sublattices construction uses the mem herm Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L141-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L141-L142

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

theorem Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub {J : Ideal A} {S : Matrix r r A} :
    S ∈ hermSub r J ↔ Sᴴ = S ∧ ∀ i j, S i j ∈ J := by sorry
