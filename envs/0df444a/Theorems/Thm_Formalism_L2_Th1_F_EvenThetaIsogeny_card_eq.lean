-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_EvenThetaIsogeny_card_eq
-- name    : Formalism.L2.Th1.F.EvenThetaIsogeny.card_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:06.128671+00:00
-- url     : https://prove2.me/theorems/cc8725e0-214b-45da-b4eb-91ef54025de9
-- title:
--   Even Theta Isogeny: card eq
-- statement:
--   The Even Theta Isogeny construction uses the card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MemOfDenEqZero.lean#L21-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MemOfDenEqZero.lean#L21-L84

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroTranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MemOfDenEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EvenThetaIsogeny
open IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α t : ℂ) (T : Finset ℂ)

theorem Formalism.L2.Th1.F.EvenThetaIsogeny.card_eq (hα : α ≠ 0) (hst : MulStable L α) (h2t : 2 * t ∈ L.lattice)
    (hT : IsFibreReps L α t T) : 2 * (T.card : ℝ) = Complex.normSq α := by sorry
