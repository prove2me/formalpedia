-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_inOp_mem
-- name    : Formalism.CountingSumsFrames.TO.inOp_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:28.145472+00:00
-- url     : https://prove2.me/theorems/34ff8308-6532-4945-a648-849cb2934104
-- title:
--   TO: in Op mem
-- statement:
--   The TO construction uses the in Op mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2568-L2569
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2568-L2569

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)
include hPi
include hφ

theorem Formalism.CountingSumsFrames.TO.inOp_mem (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : inOp L j0 Pi φ x ∈ Cset p L j0 J M := by sorry
