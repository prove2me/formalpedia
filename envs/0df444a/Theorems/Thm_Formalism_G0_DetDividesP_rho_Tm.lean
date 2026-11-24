-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_rho_Tm
-- name    : Formalism.G0.DetDividesP.rho_Tm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:06:15.566509+00:00
-- url     : https://prove2.me/theorems/5829b046-7c1a-4fa0-b0b0-5d73af7bfe4e
-- title:
--   Det Divides P: rho Tm
-- statement:
--   The Det Divides P construction uses the rho Tm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L421-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L421-L422

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

theorem Formalism.G0.DetDividesP.rho_Tm (A : Fin r → ι) (l : Fin r) : (rho K A l).mapMatrix (Tm K A) = Tm K A := by sorry
