-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_quad_inl
-- name    : Formalism.QuantumDeterminants.gn_quad_inl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:54.394482+00:00
-- url     : https://prove2.me/theorems/92fd0ce9-d431-4a44-9773-1023210e7bfc
-- title:
--   Quantum Determinants: gn quad inl
-- statement:
--   The Quantum Determinants construction uses the gn quad inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L211-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L211-L244

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

theorem Formalism.QuantumDeterminants.gn_quad_inl (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hz : inWb k r z)
    (hzz : (herm (Hpk k r) z z).re ≤ 0)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) (hc : ∀ b, c (Sum.inr b) = 0) :
    (star c ⬝ᵥ (gramM k r z z' g *ᵥ c)).re ≤ 0 := by sorry
