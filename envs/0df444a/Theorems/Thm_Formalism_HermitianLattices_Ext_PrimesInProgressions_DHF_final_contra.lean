-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_final_contra
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.final_contra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:03.673857+00:00
-- url     : https://prove2.me/theorems/3ba0a390-f1d5-4201-a740-1667cba50108
-- title:
--   DHF: final contra
-- statement:
--   The DHF construction uses the final contra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishA.lean#L155-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishA.lean#L155-L191

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.final_contra (q A K0 a b l : ℝ) (K : ℕ) (hq0 : 0 < q) (hq : q ≤ 1 / 4) (hl : l = -Real.log q)
    (hA : 1 ≤ A) (hK3 : 3 ≤ K) (hK0 : 0 < K0) (ha0 : 0 ≤ a) (ha : a * (2 * l + 2) ≤ 1) (hb : 0 ≤ b)
    (hKab : (K : ℝ) ≤ a * K0 + b) (hbig : b + 64 * A * Real.exp (l * b) < K0)
    (hmain : q ^ K ≤ 2 * A * K * Real.exp (-K0) + K * (q ^ 2 / 8) ^ (K - 1) + K * (q / 4) ^ K) : False := by sorry
