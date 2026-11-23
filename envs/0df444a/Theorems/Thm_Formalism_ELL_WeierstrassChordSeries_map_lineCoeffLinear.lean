-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_map_lineCoeffLinear
-- name    : Formalism.ELL.WeierstrassChordSeries.map_lineCoeffLinear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:34.278623+00:00
-- url     : https://prove2.me/theorems/d609add0-a12d-4cc6-9585-2b61bf7b681c
-- title:
--   Weierstrass Chord Series: map line Coeff Linear
-- statement:
--   The Weierstrass Chord Series construction uses the map line Coeff Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L74-L78

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

theorem Formalism.ELL.WeierstrassChordSeries.map_lineCoeffLinear (a1 a3 a4 a6 l n : R) :
    φ (c1 a1 a3 a4 a6 l n) = c1 (φ a1) (φ a3) (φ a4) (φ a6) (φ l) (φ n) := by sorry
