-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupLinearJets_coeff_one_subst
-- name    : Formalism.ELL.FormalGroupLinearJets.coeff_one_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:46.17191+00:00
-- url     : https://prove2.me/theorems/b87a2adc-ea96-48e2-8652-b68ac227652c
-- title:
--   Formal Group Linear Jets: coeff one subst
-- statement:
--   The Formal Group Linear Jets construction uses the coeff one subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsOne.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsOne.lean#L19-L30

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupLinearJets
variable {K : Type u} [CommRing K]

theorem Formalism.ELL.FormalGroupLinearJets.coeff_one_subst {φ a : PowerSeries K} (ha : constantCoeff a = 0) :
    coeff 1 (φ.subst a) = coeff 1 φ * coeff 1 a := by sorry
