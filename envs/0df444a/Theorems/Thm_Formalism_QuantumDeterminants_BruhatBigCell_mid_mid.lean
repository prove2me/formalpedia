-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_mid_mid
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.mid_mid
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:12.283317+00:00
-- url     : https://prove2.me/theorems/139a723e-284f-4ed6-8b3f-886132644ca9
-- title:
--   Bruhat Big Cell: mid mid
-- statement:
--   The Bruhat Big Cell construction uses the mid mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L97-L102

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
variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

theorem Formalism.QuantumDeterminants.BruhatBigCell.mid_mid (p q : Fin (k + 1)) : bigCell k r c μ (wI k r p) (wI k r q) = μ p q := by sorry
