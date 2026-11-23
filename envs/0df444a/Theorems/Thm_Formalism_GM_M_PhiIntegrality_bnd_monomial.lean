-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_monomial
-- name    : Formalism.GM.M.PhiIntegrality.bnd_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:53.769508+00:00
-- url     : https://prove2.me/theorems/6471266a-d7ca-483f-9302-48eb06ec0bbe
-- title:
--   Phi Integrality: bnd monomial
-- statement:
--   The Phi Integrality construction uses the bnd monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L66-L74

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

theorem Formalism.GM.M.PhiIntegrality.bnd_monomial (m : σ →₀ ℕ) (n : ℕ) : Bnd 1 (monomial m ((n : ℕ) : ℚ_[p])) := by sorry
