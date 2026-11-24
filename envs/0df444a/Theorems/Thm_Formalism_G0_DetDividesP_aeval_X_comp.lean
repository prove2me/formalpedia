-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_aeval_X_comp
-- name    : Formalism.G0.DetDividesP.aeval_X_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:34.851538+00:00
-- url     : https://prove2.me/theorems/38dec159-2d67-4f10-b3a7-5cf88057c084
-- title:
--   Det Divides P: aeval X comp
-- statement:
--   The Det Divides P construction uses the aeval X comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L509-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L509-L514

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

theorem Formalism.G0.DetDividesP.aeval_X_comp {σ τ : Type} (f : σ → τ) (p : MvPolynomial σ K) :
    aeval (fun q => (X (f q) : MvPolynomial τ K)) p = rename f p := by sorry
