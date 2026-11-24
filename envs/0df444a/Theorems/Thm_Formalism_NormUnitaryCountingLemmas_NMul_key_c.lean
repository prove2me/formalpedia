-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_key_c
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.key_c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:37.833296+00:00
-- url     : https://prove2.me/theorems/2fe4b212-5c5f-4de8-bd48-10fb8dedbbd2
-- title:
--   NMul: key c
-- statement:
--   The NMul construction uses the key c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L124-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L124-L198

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.NMul

theorem Formalism.NormUnitaryCountingLemmas.NMul.key_c {N n : ℕ} {ν : Fin N → ℕ} {F G : MvPolynomial (Fin N × Fin n) ℂ}
    (hF : ∀ a ∈ F.support, ∀ j, blockDeg a j = ν j) (c : Fin N × Fin n →₀ ℕ) :
    ‖∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        coeff p.1 F * coeff p.2 G‖ ^ 2 * bweight c ≤
      ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
        (‖coeff p.1 F‖ ^ 2 * bweight p.1) * (‖coeff p.2 G‖ ^ 2 * bweight p.2) := by sorry
