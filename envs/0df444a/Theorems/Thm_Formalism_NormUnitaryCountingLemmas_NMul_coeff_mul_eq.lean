-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_coeff_mul_eq
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.coeff_mul_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:42.180955+00:00
-- url     : https://prove2.me/theorems/15218216-f22f-4110-9823-a5a5250ff73c
-- title:
--   NMul: coeff mul eq
-- statement:
--   The NMul construction uses the coeff mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L200-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L200-L216

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

theorem Formalism.NormUnitaryCountingLemmas.NMul.coeff_mul_eq {N n : ℕ} (F G : MvPolynomial (Fin N × Fin n) ℂ)
    (c : Fin N × Fin n →₀ ℕ) :
    coeff c (F * G) = ∑ p ∈ (F.support ×ˢ G.support).filter (fun p => p.1 + p.2 = c),
      coeff p.1 F * coeff p.2 G := by sorry
