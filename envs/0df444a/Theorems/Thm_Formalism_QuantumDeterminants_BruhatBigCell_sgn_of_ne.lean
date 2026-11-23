-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_sgn_of_ne
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.sgn_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:33.733131+00:00
-- url     : https://prove2.me/theorems/8f2bded9-3991-4675-b7df-6e5fad7c4d82
-- title:
--   Bruhat Big Cell: sgn of ne
-- statement:
--   The Bruhat Big Cell construction uses the sgn of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L31-L32

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
variable {k r : ℕ}

theorem Formalism.QuantumDeterminants.BruhatBigCell.sgn_of_ne (p : Fin (2 * r + k + 1)) (h : p.val ≠ r + k) : sgn k r p = 1 := by sorry
