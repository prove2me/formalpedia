-- Prove2me | Theorems.Thm_Formalism_GM_FockB_pos_ne
-- name    : Formalism.GM.FockB.pos_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:13.842279+00:00
-- url     : https://prove2.me/theorems/96273bcc-1894-4780-95b4-eb6a5b14613f
-- title:
--   Fock B: pos ne
-- statement:
--   The Fock B construction uses the pos ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L439-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L439-L440

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} (D : BlockData N)
variable (p : ℕ) [Fact p.Prime]
variable {D}

theorem Formalism.GM.FockB.pos_ne (hB : D.BlockOK) {i i' : Fin D.T.t} (h : i ≠ i') : D.T.pos i ≠ D.T.pos i' := by sorry
