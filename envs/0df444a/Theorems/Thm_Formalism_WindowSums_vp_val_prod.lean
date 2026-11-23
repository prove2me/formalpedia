-- Prove2me | Theorems.Thm_Formalism_WindowSums_vp_val_prod
-- name    : Formalism.WindowSums.vp_val_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:09.199007+00:00
-- url     : https://prove2.me/theorems/5aaba6f1-faba-479c-93ca-6f9c0eb9ed79
-- title:
--   Window Sums: vp val prod
-- statement:
--   The Window Sums construction uses the vp val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ValProd.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ValProd.lean#L21-L33

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.WindowSums
open Finset
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem Formalism.WindowSums.vp_val_prod {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ_[ℓ])
    (h : ∀ i ∈ S, f i ≠ 0) :
    (∏ i ∈ S, f i) ≠ 0 ∧ (∏ i ∈ S, f i).valuation = ∑ i ∈ S, (f i).valuation := by sorry
