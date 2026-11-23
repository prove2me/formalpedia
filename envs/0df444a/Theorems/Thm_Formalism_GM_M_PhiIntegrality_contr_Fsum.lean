-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_Fsum
-- name    : Formalism.GM.M.PhiIntegrality.contr_Fsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:54.663797+00:00
-- url     : https://prove2.me/theorems/092fe0bb-7045-4a13-a8d9-0cad804efa8d
-- title:
--   Phi Integrality: contr Fsum
-- statement:
--   The Phi Integrality construction uses the contr Fsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L211-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L211-L240

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
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

theorem Formalism.GM.M.PhiIntegrality.contr_Fsum {ι : Type} [DecidableEq ι]
    (D : ι → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]))
    (hcomm : ∀ a b, Commute (D a) (D b))
    (hdiv : ∀ a k, Contr 1 ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (D a ^ k)))
    {Mc : ℝ} (hM1 : 1 ≤ Mc) (N : ℕ)
    (hM : ∀ j ≤ N, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc) (S : Finset ι) :
    ∀ j ≤ N, Contr (Mc ^ S.card) ((((j.factorial : ℚ_[p]) ^ 2))⁻¹ • ((∑ c ∈ S, D c) ^ j)) := by sorry
