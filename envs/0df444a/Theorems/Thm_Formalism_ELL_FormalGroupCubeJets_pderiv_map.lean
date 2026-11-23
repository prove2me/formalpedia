-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_pderiv_map
-- name    : Formalism.ELL.FormalGroupCubeJets.pderiv_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:51.069482+00:00
-- url     : https://prove2.me/theorems/04556609-ac4c-47f3-ab5e-137e63d61c4c
-- title:
--   Formal Group Cube Jets: pderiv map
-- statement:
--   The Formal Group Cube Jets construction uses the pderiv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsCube.lean#L41-L47

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupCubeJets
open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.ELL.FormalGroupCubeJets.pderiv_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (i : σ)
    (g : MvPowerSeries σ R) :
    MvPowerSeries.pderiv S i (MvPowerSeries.map f g) =
      MvPowerSeries.map f (MvPowerSeries.pderiv R i g) := by sorry
