-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_Q_sub
-- name    : Formalism.ELL.FormalGroupQuadraticJets.Q_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:55.274931+00:00
-- url     : https://prove2.me/theorems/d89438ad-1c66-495c-ab2f-eab4107f19d0
-- title:
--   Formal Group Quadratic Jets: Q sub
-- statement:
--   The Formal Group Quadratic Jets construction uses the Q sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L20-L21

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

theorem Formalism.ELL.FormalGroupQuadraticJets.Q_sub (f g : MvPowerSeries (Fin 2) K) : Q (f - g) = Q f - Q g := by sorry
