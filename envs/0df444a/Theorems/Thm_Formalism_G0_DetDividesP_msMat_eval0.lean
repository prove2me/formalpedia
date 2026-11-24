-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_msMat_eval0
-- name    : Formalism.G0.DetDividesP.msMat_eval0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:06.865611+00:00
-- url     : https://prove2.me/theorems/8a6c3f3f-ed69-4ac6-99ba-fc275e272820
-- title:
--   Det Divides P: ms Mat eval0
-- statement:
--   The Det Divides P construction uses the ms Mat eval0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L65-L73

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {L : Type} [Field L] {r : ℕ}

theorem Formalism.G0.DetDividesP.msMat_eval0 (g : GL (Fin r) L) :
    (msMat g).map (Polynomial.evalRingHom 0) =
      g.1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) * (g⁻¹ : GL (Fin r) L).1 := by sorry
