-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadAdj_rep_inj
-- name    : Formalism.HermitianLattices.Ext.L3.QuadAdj.rep_inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:40:22.464334+00:00
-- url     : https://prove2.me/theorems/f326fbf5-c7fd-4c5f-8574-13a16fa73935
-- title:
--   Quad Adj: rep inj
-- statement:
--   The Quad Adj construction uses the rep inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandDA.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandDA.lean#L57-L62

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

theorem Formalism.HermitianLattices.Ext.L3.QuadAdj.rep_inj {a b a' b' : F}
    (h : AdjoinRoot.of (X ^ 2 - C c) a + AdjoinRoot.of _ b * AdjoinRoot.root _ =
      AdjoinRoot.of _ a' + AdjoinRoot.of _ b' * AdjoinRoot.root _) : a = a' ∧ b = b' := by sorry
