-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lineCoeffCubic_mem
-- name    : Formalism.ELL.WeierstrassChordSeries.lineCoeffCubic_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:39.843783+00:00
-- url     : https://prove2.me/theorems/1e627fb2-7f6f-4b25-8c1a-46ecfb8b2991
-- title:
--   Weierstrass Chord Series: line Coeff Cubic mem
-- statement:
--   The Weierstrass Chord Series construction uses the line Coeff Cubic mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L91-L95

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
variable (T : Subring R)

theorem Formalism.ELL.WeierstrassChordSeries.lineCoeffCubic_mem {a2 a4 a6 l : R} (h2 : a2 ∈ T) (h4 : a4 ∈ T) (h6 : a6 ∈ T) (hl : l ∈ T) :
    c3 a2 a4 a6 l ∈ T := by sorry
