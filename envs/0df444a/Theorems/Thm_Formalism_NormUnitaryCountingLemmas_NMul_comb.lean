-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_comb
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:33.629051+00:00
-- url     : https://prove2.me/theorems/a081678b-b781-49ac-8b87-d5693a4df063
-- title:
--   NMul: comb
-- statement:
--   The NMul construction uses the comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L77-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L77-L122

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

theorem Formalism.NormUnitaryCountingLemmas.NMul.comb {N n : ℕ} (ν : Fin N → ℕ) (sF sG : Finset (Fin N × Fin n →₀ ℕ))
    (hF : ∀ a ∈ sF, ∀ j, blockDeg a j = ν j) (c : Fin N × Fin n →₀ ℕ) :
    ∑ p ∈ (sF ×ˢ sG).filter (fun p => p.1 + p.2 = c), ∏ j, ∏ k, (c (j, k)).choose (p.1 (j, k)) ≤
      ∏ j, (blockDeg c j).choose (ν j) := by sorry
