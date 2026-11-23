-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_map_lineCoeffConst
-- name    : Formalism.ELL.WeierstrassChordSeries.map_lineCoeffConst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:33.584284+00:00
-- url     : https://prove2.me/theorems/bb0b1331-e93a-4384-9704-240999f5e980
-- title:
--   Weierstrass Chord Series: map line Coeff Const
-- statement:
--   The Weierstrass Chord Series construction uses the map line Coeff Const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L79-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L79-L80

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

theorem Formalism.ELL.WeierstrassChordSeries.map_lineCoeffConst (a3 a6 n : R) : φ (c0 a3 a6 n) = c0 (φ a3) (φ a6) (φ n) := by sorry
