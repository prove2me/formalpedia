-- Prove2me | Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_cyc_inertia
-- name    : Formalism.TwoAdicCyclotomicDecomposition.odd_cyc_inertia
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:30:34.628063+00:00
-- url     : https://prove2.me/theorems/e6da4625-3bf0-4b5f-bae0-354cf711b0ac
-- title:
--   Two Adic Cyclotomic Decomposition: odd cyc inertia
-- statement:
--   The Two Adic Cyclotomic Decomposition construction uses the odd cyc inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L148-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/OddEqOneOfSubOneMem.lean#L148-L176

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition

theorem Formalism.TwoAdicCyclotomicDecomposition.odd_cyc_inertia {L : Type} [Field L] [NumberField L] {n : ℕ} {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ n)) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})]
    (σ : Gal(L/ℚ)) (hσ : ∀ x : 𝓞 L, σ • x - x ∈ P) : hζ.autToPow ℚ σ = 1 := by sorry
