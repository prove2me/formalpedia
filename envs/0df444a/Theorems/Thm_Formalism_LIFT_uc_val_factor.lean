-- Prove2me | Theorems.Thm_Formalism_LIFT_uc_val_factor
-- name    : Formalism.LIFT.uc_val_factor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:57.903909+00:00
-- url     : https://prove2.me/theorems/c310f831-16eb-4711-8b8d-5757596850bf
-- title:
--   LIFT: uc val factor
-- statement:
--   The LIFT construction uses the uc val factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L252-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UChase.lean#L252-L285

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT

theorem Formalism.LIFT.uc_val_factor (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (M s : ℕ) (J : Finset ℤ) (hs : 1 ≤ s)
    (h2 : ℓ = 2 → 2 ≤ s) (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s) (hJ : 0 ∉ J) :
    ∃ ν : ℤ_[ℓ], (ℓ : ℤ_[ℓ]) ^ eU ℓ M s J =
      ((∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
        ∏ i ∈ Finset.Icc 1 M, ((u : ℤ_[ℓ]) ^ i - 1)) * ν := by sorry
