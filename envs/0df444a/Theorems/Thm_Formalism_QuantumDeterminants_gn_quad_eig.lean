-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_quad_eig
-- name    : Formalism.QuantumDeterminants.gn_quad_eig
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:02.426796+00:00
-- url     : https://prove2.me/theorems/fe2af463-5b10-4185-947c-e25e93b07d5e
-- title:
--   Quantum Determinants: gn quad eig
-- statement:
--   The Quantum Determinants construction uses the gn quad eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L43-L65

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

theorem Formalism.QuantumDeterminants.gn_quad_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (d : ι → ℂ) :
    star ((hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ d) ⬝ᵥ
        (A *ᵥ ((hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ d)) =
      ∑ i, ((hA.eigenvalues i * Complex.normSq (d i) : ℝ) : ℂ) := by sorry
