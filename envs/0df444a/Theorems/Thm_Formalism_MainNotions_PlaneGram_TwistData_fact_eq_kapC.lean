-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fact_eq_kapC
-- name    : Formalism.MainNotions.PlaneGram.TwistData.fact_eq_kapC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:56.741797+00:00
-- url     : https://prove2.me/theorems/1f00d7a8-0e4a-4bac-9f05-53d98dc4d70e
-- title:
--   Twist Data: fact eq kap C
-- statement:
--   The Twist Data construction uses the fact eq kap C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L173-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/GlobalTheory.lean#L173-L191

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem Formalism.MainNotions.PlaneGram.TwistData.fact_eq_kapC {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K}
    {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K} (hdig : D.DigOK v p cst gam) {ζ : D.EM}
    (hζ : D.LabLowE p ζ) :
    (fact (D.collapseExponent p ζ) : K) * (fact (D.tpE ζ) : K) =
      D.kapC cst ζ * (∏ t, gam t (D.labF ζ t) (D.wF ζ t)) * (fact ζ : K) := by sorry
