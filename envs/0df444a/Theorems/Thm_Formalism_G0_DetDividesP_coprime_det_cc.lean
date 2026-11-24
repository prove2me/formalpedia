-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_coprime_det_cc
-- name    : Formalism.G0.DetDividesP.coprime_det_cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:51.737227+00:00
-- url     : https://prove2.me/theorems/54846a01-c06e-49b6-bf64-aa700257a990
-- title:
--   Det Divides P: coprime det cc
-- statement:
--   The Det Divides P construction uses the coprime det cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L456-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L456-L495

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

theorem Formalism.G0.DetDividesP.coprime_det_cc (A : Fin r → ι) (hA : Function.Injective A) (lst : Fin r) :
    IsRelPrime (Tm K A).det (((Tm K A).adjugate.mulVec (Wv K A)) lst) := by sorry
