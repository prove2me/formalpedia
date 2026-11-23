-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_map_lineCoeffQuadratic
-- name    : Formalism.ELL.WeierstrassChordSeries.map_lineCoeffQuadratic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:31.118535+00:00
-- url     : https://prove2.me/theorems/8c7b27b0-3fa4-485e-9cd6-4f328889beb4
-- title:
--   Weierstrass Chord Series: map line Coeff Quadratic
-- statement:
--   The Weierstrass Chord Series construction uses the map line Coeff Quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L69-L73

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

theorem Formalism.ELL.WeierstrassChordSeries.map_lineCoeffQuadratic (a1 a2 a3 a4 a6 l n : R) :
    φ (c2 a1 a2 a3 a4 a6 l n) = c2 (φ a1) (φ a2) (φ a3) (φ a4) (φ a6) (φ l) (φ n) := by sorry
