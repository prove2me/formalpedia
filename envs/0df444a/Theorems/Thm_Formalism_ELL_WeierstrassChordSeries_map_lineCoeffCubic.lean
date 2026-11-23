-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_map_lineCoeffCubic
-- name    : Formalism.ELL.WeierstrassChordSeries.map_lineCoeffCubic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:31.845844+00:00
-- url     : https://prove2.me/theorems/4e329cd2-34da-443d-b8d7-0ed39f6929fa
-- title:
--   Weierstrass Chord Series: map line Coeff Cubic
-- statement:
--   The Weierstrass Chord Series construction uses the map line Coeff Cubic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L67-L68

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
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
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {R : Type*} [CommRing R]
variable {R' : Type*} [CommRing R'] (φ : R →+* R')

theorem Formalism.ELL.WeierstrassChordSeries.map_lineCoeffCubic (a2 a4 a6 l : R) : φ (c3 a2 a4 a6 l) = c3 (φ a2) (φ a4) (φ a6) (φ l) := by sorry
