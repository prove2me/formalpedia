-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanA_mem_pow_of_mul_mem
-- name    : Formalism.HermitianLattices.Ext.L3.MeanA.mem_pow_of_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:12.576436+00:00
-- url     : https://prove2.me/theorems/7bf819f7-16e5-4450-b707-4acc68abdf31
-- title:
--   Mean A: mem pow of mul mem
-- statement:
--   The Mean A construction uses the mem pow of mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulSubOneMemPow.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsMulSubOneMemPow.lean#L21-L26

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
set_option linter.deprecated false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanA

theorem Formalism.HermitianLattices.Ext.L3.MeanA.mem_pow_of_mul_mem {R : Type*} [CommRing R] {𝔭 : Ideal R} (h𝔭 : 𝔭.IsMaximal) {t c : R}
    (ht : t ∉ 𝔭) {k : ℕ} (h : t * c ∈ 𝔭 ^ k) : c ∈ 𝔭 ^ k := by sorry
