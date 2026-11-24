-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_constantCoeff_conj_diagonal_rescale
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.constantCoeff_conj_diagonal_rescale
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:14.658569+00:00
-- url     : https://prove2.me/theorems/ee30919a-62a8-4158-9044-3c3d35db64bc
-- title:
--   Frobenius Period Change: constant Coeff conj diagonal rescale
-- statement:
--   The Frobenius Period Change construction uses the constant Coeff conj diagonal rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L1152-L1180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L1152-L1180

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.constantCoeff_conj_diagonal_rescale {L : Type} [Field L] {n : ℕ} (Γ G : Matrix (Fin n) (Fin n) L⟦X⟧) (υ : L)
    (a : Fin n → ℕ)
    (h : Γ * (G * Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)).map (rescale υ) =
      G * Matrix.diagonal (fun j => (X : L⟦X⟧) ^ a j)) :
    Γ.map constantCoeff * G.map constantCoeff * Matrix.diagonal (fun j => υ ^ a j) =
      G.map constantCoeff := by sorry
