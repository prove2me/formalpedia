-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lineCoeffQuadratic_mem
-- name    : Formalism.ELL.WeierstrassChordSeries.lineCoeffQuadratic_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:24.798794+00:00
-- url     : https://prove2.me/theorems/bf38df08-a74f-4644-aefa-d877d5a8bab2
-- title:
--   Weierstrass Chord Series: line Coeff Quadratic mem
-- statement:
--   The Weierstrass Chord Series construction uses the line Coeff Quadratic mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L96-L101

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

theorem Formalism.ELL.WeierstrassChordSeries.lineCoeffQuadratic_mem {a1 a2 a3 a4 a6 l n : R} (h1 : a1 ∈ T) (h2 : a2 ∈ T) (h3 : a3 ∈ T) (h4 : a4 ∈ T)
    (h6 : a6 ∈ T) (hl : l ∈ T) (hn : n ∈ T) : c2 a1 a2 a3 a4 a6 l n ∈ T := by sorry
