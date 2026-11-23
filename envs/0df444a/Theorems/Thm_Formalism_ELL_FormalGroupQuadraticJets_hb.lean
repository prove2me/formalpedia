-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
-- name    : Formalism.ELL.FormalGroupQuadraticJets.hb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:16.286777+00:00
-- url     : https://prove2.me/theorems/02ee8fb1-f044-488e-9c8f-5e8471ecdb69
-- title:
--   Formal Group Quadratic Jets: hb
-- statement:
--   The Formal Group Quadratic Jets construction uses the hb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L144-L149

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.ELL.FormalGroupQuadraticJets.hb : ∀ j, MvPowerSeries.constantCoeff
    ((![PowerSeries.X, (0 : PowerSeries K)] : Fin 2 → PowerSeries K) j) = 0 := by sorry
