-- Prove2me | Theorems.Thm_Formalism_G0_DetDividesP_not_mem_vars_of_degreeOf
-- name    : Formalism.G0.DetDividesP.not_mem_vars_of_degreeOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:21.855989+00:00
-- url     : https://prove2.me/theorems/677d3bbd-42e2-468b-afa8-b89e8e5561e6
-- title:
--   Det Divides P: not mem vars of degree Of
-- statement:
--   The Det Divides P construction uses the not mem vars of degree Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L302-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean#L302-L310

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

theorem Formalism.G0.DetDividesP.not_mem_vars_of_degreeOf {σ : Type} {p : MvPolynomial σ K} {x : σ} (h : degreeOf x p = 0) :
    x ∉ p.vars := by sorry
