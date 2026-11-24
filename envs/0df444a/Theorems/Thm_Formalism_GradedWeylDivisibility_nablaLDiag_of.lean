-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_nablaLDiag_of
-- name    : Formalism.GradedWeylDivisibility.nablaLDiag_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:24.251944+00:00
-- url     : https://prove2.me/theorems/b654a6a5-1b16-4c8e-81b3-250d8b43e324
-- title:
--   Graded Weyl Divisibility: nabla LDiag of
-- statement:
--   The Graded Weyl Divisibility construction uses the nabla LDiag of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLDiag.lean#L9-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/NablaLDiag.lean#L9-L32

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLBasis
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.nablaLDiag_of (h1 : RowActMul) (h2 : RowActDiagWeight) (h3 : NablaLBasis) : NablaLDiag := by sorry
