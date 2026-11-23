-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_linear
-- name    : Formalism.GM.M.PhiIntegrality.bnd_linear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:45.695027+00:00
-- url     : https://prove2.me/theorems/bfc2260a-eb6b-4dda-ab4d-57d6df73d419
-- title:
--   Phi Integrality: bnd linear
-- statement:
--   The Phi Integrality construction uses the bnd linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L53-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L53-L64

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type}

theorem Formalism.GM.M.PhiIntegrality.bnd_linear (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) {C B : ℝ} (hC : 0 ≤ C)
    (hT : ∀ m, Bnd C (T (monomial m 1))) {u : MvPolynomial σ ℚ_[p]} (hu : Bnd B u) (hB : 0 ≤ B) :
    Bnd (B * C) (T u) := by sorry
