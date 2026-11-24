-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_isWH_rename
-- name    : Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.isWH_rename
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:18:04.271259+00:00
-- url     : https://prove2.me/theorems/b2460022-402d-4d7d-b528-cc581e93dafc
-- title:
--   Principal Injective Common Range: is WH rename
-- statement:
--   The Principal Injective Common Range construction uses the is WH rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearHypothesisTwo.lean#L33-L43

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
variable {R : Type*} [CommRing R]

theorem Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange.isWH_rename {N N' n : ℕ} (hN : N ≤ N') (ν : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) R)
    (hF : F.IsWeightedHomogeneous (blockWt N n) ν) :
    (rename (fun p : Fin N × Fin n => (Fin.castLE hN p.1, p.2)) F).IsWeightedHomogeneous
      (blockWt N' n) (extW ν) := by sorry
