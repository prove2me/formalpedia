-- Prove2me | Theorems.Thm_Formalism_L2_Th1_F_EvenThetaIsogeny_thetaZero_periodLattice_eq
-- name    : Formalism.L2.Th1.F.EvenThetaIsogeny.thetaZero_periodLattice_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:25.482021+00:00
-- url     : https://prove2.me/theorems/17062fde-7854-46e1-9cb2-61281293308f
-- title:
--   Even Theta Isogeny: theta Zero period Lattice eq
-- statement:
--   The Even Theta Isogeny construction uses the theta Zero period Lattice eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MemOfDenEqZero.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/MemOfDenEqZero.lean#L90-L94

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroTranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MemOfDenEqZero
import Theorems.Thm_Formalism_L2_Th1_F_ThetaZeroHermitianLemmas_thetaZero_periodLattice_eq

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

theorem Formalism.L2.Th1.F.EvenThetaIsogeny.thetaZero_periodLattice_eq (w : ℂ) : th0 L t w = (opU L t (sgStar L) 0)⁻¹ * (sgStar L (w + t) *
    Complex.exp (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2)) := by sorry
