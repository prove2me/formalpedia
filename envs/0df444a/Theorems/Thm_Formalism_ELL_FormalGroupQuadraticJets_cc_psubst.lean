-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_psubst
-- name    : Formalism.ELL.FormalGroupQuadraticJets.cc_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:37.17181+00:00
-- url     : https://prove2.me/theorems/918aec08-a49e-400a-a779-906cc1b9773a
-- title:
--   Formal Group Quadratic Jets: cc psubst
-- statement:
--   The Formal Group Quadratic Jets construction uses the cc psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L23-L26

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type*} [CommRing K]

theorem Formalism.ELL.FormalGroupQuadraticJets.cc_psubst {τ : Type*} [Finite τ] {a : MvPowerSeries τ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (f.subst a) = PowerSeries.constantCoeff f := by sorry
