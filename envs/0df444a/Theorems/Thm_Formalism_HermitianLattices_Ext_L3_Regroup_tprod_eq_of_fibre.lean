-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Regroup_tprod_eq_of_fibre
-- name    : Formalism.HermitianLattices.Ext.L3.Regroup.tprod_eq_of_fibre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:12.91886+00:00
-- url     : https://prove2.me/theorems/c8b3f4f1-a167-4bbf-b4cc-3600cb221ecc
-- title:
--   Regroup: tprod eq of fibre
-- statement:
--   The Regroup construction uses the tprod eq of fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LValEtaEqLValEtaF.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LValEtaEqLValEtaF.lean#L11-L15

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
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
open Formalism.HermitianLattices.Ext.L3.Regroup

theorem Formalism.HermitianLattices.Ext.L3.Regroup.tprod_eq_of_fibre {α β : Type*} {f : α → ℝ} (π : α → β) {g : β → ℝ} (hf : Multipliable f)
    (hg : ∀ b, HasProd (fun c : {x // π x = b} => f c.1) (g b)) : ∏' a, f a = ∏' b, g b := by sorry
