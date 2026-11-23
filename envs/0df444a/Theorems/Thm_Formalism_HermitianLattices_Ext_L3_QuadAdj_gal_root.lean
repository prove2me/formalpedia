-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadAdj_gal_root
-- name    : Formalism.HermitianLattices.Ext.L3.QuadAdj.gal_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:12.594098+00:00
-- url     : https://prove2.me/theorems/1057629c-3584-43e3-a830-567375400a15
-- title:
--   Quad Adj: gal root
-- statement:
--   The Quad Adj construction uses the gal root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandDA.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandDA.lean#L92-L101

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.QuadAdj
variable {F : Type*} [Field F] (c : F)
variable [Fact (Irreducible (X ^ 2 - C c : F[X]))]

theorem Formalism.HermitianLattices.Ext.L3.QuadAdj.gal_root (τ : AdjoinRoot (X ^ 2 - C c) ≃ₐ[F] AdjoinRoot (X ^ 2 - C c)) :
    τ (AdjoinRoot.root _) = AdjoinRoot.root _ ∨ τ (AdjoinRoot.root _) = -AdjoinRoot.root _ := by sorry
