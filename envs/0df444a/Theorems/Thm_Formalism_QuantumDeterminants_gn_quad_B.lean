-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_quad_B
-- name    : Formalism.QuantumDeterminants.gn_quad_B
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:58.539217+00:00
-- url     : https://prove2.me/theorems/2f3c90cd-596c-4425-a133-1ac1301fc56b
-- title:
--   Quantum Determinants: gn quad B
-- statement:
--   The Quantum Determinants construction uses the gn quad B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L165-L172

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

theorem Formalism.QuantumDeterminants.gn_quad_B (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    star c ⬝ᵥ (gramM k r z z' g *ᵥ c) =
      herm (Hpk k r) (gnB k r z z' g *ᵥ c) (gnB k r z z' g *ᵥ c) := by sorry
