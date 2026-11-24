-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_rho_adj
-- name    : Formalism.G0.DetDividesP.rho_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:07.768588+00:00
-- url     : https://prove2.me/theorems/4804ad2b-f416-49f3-8eba-d26a6d515ab4
-- title:
--   Det Divides P: rho adj
-- statement:
--   The Det Divides P construction uses the rho adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L424-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L424-L428

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
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

theorem Formalism.G0.DetDividesP.rho_adj (A : Fin r → ι) (l i j : Fin r) : rho K A l ((Tm K A).adjugate i j) = (Tm K A).adjugate i j := by sorry
