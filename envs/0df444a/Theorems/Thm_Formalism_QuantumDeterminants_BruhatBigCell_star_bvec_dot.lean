-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_star_bvec_dot
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.star_bvec_dot
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:02.424168+00:00
-- url     : https://prove2.me/theorems/9280d2f8-7be8-42f2-b155-b268e9b8c640
-- title:
--   Bruhat Big Cell: star bvec dot
-- statement:
--   The Bruhat Big Cell construction uses the star bvec dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L216-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L216-L220

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

theorem Formalism.QuantumDeterminants.BruhatBigCell.star_bvec_dot {m : ℕ} (e : Fin m) (w : Fin m → ℂ) : star (bvec e) ⬝ᵥ w = w e := by sorry
