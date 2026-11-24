-- Prove2me | Theorems.Thm_Formalism_REAL_omega_eigenvalue_on_span
-- name    : Formalism.REAL.omega_eigenvalue_on_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:24:44.54505+00:00
-- url     : https://prove2.me/theorems/bbd8d87a-027d-4bc7-abbd-d3e6100292f8
-- title:
--   REAL: omega eigenvalue on span
-- statement:
--   The REAL construction uses the omega eigenvalue on span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L415-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L415-L431

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.omega_eigenvalue_on_span (hk : KCasSpan) (hca : CasArr) (ha : ArrModule) {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ μ : Fin n → ℝ} {u : V} {y : Arr V n 1}
    (hg : GlRel E) (hΛ : KHighest ε E Λ u) (hy : y ∈ arrV0 ε E u 1)
    (hyh : KHighest ε (arrE E 1) μ y) {G : Arr V n 1} (hG : G ∈ kSpan ε (arrE E 1) y) :
    OmS ε E (0 : Fin 1) G = (((ckv ε μ - n - ckv ε Λ) / 2 : ℝ) : ℂ) • G := by sorry
