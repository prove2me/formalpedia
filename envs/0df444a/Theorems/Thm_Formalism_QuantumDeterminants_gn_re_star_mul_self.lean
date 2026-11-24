-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_re_star_mul_self
-- name    : Formalism.QuantumDeterminants.gn_re_star_mul_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:04.181933+00:00
-- url     : https://prove2.me/theorems/28ff44d6-590a-41e1-b9ba-3b84c179c8fd
-- title:
--   Quantum Determinants: gn re star mul self
-- statement:
--   The Quantum Determinants construction uses the gn re star mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L37-L41

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
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

theorem Formalism.QuantumDeterminants.gn_re_star_mul_self (w : ℂ) : (star w * w).re = Complex.normSq w := by sorry
