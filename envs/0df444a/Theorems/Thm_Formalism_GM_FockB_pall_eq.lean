-- Prove2me | Theorems.Thm_Formalism_GM_FockB_pall_eq
-- name    : Formalism.GM.FockB.pall_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:06.889864+00:00
-- url     : https://prove2.me/theorems/ab203bd8-453f-40d2-a6fa-76bbbd25dbdd
-- title:
--   Fock B: pall eq
-- statement:
--   The Fock B construction uses the pall eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L420-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L420-L423

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

theorem Formalism.GM.FockB.pall_eq (j : Fin D.T.t → ℕ) (jp : ℕ) (Y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    D.Pall p j jp Y = chainP (wA D) (eA D) (zA D) (sA D) (zzA D) (oA D j jp) (nA D j jp) (LA D) Y := by sorry
