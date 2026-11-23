-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_eq_ext_res
-- name    : Formalism.GM.M.FB.eq_ext_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:36.765291+00:00
-- url     : https://prove2.me/theorems/d3779a5d-eecf-4b2e-a883-9814923aa349
-- title:
--   FB: eq ext res
-- statement:
--   The FB construction uses the eq ext res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L377-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L377-L390

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.M.FB.eq_ext_res (n : ℕ) (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ)
    (hZ : ∀ c, c ≠ ρ → m (Fin.last N, c) = 0) (hrow : ∑ c, m (Fin.last N, c) = n) :
    m = ext n ρ (res m) := by sorry
