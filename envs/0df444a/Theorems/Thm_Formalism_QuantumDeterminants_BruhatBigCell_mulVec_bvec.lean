-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_mulVec_bvec
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.mulVec_bvec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:47.253346+00:00
-- url     : https://prove2.me/theorems/24179c5f-b2bc-4b98-9790-072d2cd46712
-- title:
--   Bruhat Big Cell: mul Vec bvec
-- statement:
--   The Bruhat Big Cell construction uses the mul Vec bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L222-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L222-L224

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic

theorem Formalism.QuantumDeterminants.BruhatBigCell.mulVec_bvec {k r : ℕ} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (e i : Fin (2 * r + k + 1)) : (M *ᵥ bvec e) i = M i e := by sorry
