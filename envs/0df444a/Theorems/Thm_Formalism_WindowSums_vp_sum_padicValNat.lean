-- Prove2me | Theorems.Thm_Formalism_WindowSums_vp_sum_padicValNat
-- name    : Formalism.WindowSums.vp_sum_padicValNat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:39:33.188721+00:00
-- url     : https://prove2.me/theorems/4921e719-1387-415b-b23b-c160e31abf83
-- title:
--   Window Sums: vp sum padic Val Nat
-- statement:
--   The Window Sums construction uses the vp sum padic Val Nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ValProd.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WindowSums/AnnihilatorPolynomials/ValProd.lean#L48-L55

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

theorem Formalism.WindowSums.vp_sum_padicValNat (M : ℕ) :
    ∑ i ∈ Finset.Icc 1 M, padicValNat ℓ i = padicValNat ℓ M.factorial := by sorry
