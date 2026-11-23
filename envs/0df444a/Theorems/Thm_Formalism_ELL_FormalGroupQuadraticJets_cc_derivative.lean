-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_derivative
-- name    : Formalism.ELL.FormalGroupQuadraticJets.cc_derivative
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:13.04729+00:00
-- url     : https://prove2.me/theorems/49b54e5e-f37e-48b4-b2a0-3f29a11c39fa
-- title:
--   Formal Group Quadratic Jets: cc derivative
-- statement:
--   The Formal Group Quadratic Jets construction uses the cc derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L28-L31

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

theorem Formalism.ELL.FormalGroupQuadraticJets.cc_derivative (f : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.derivative K f) = PowerSeries.coeff 1 f := by sorry
