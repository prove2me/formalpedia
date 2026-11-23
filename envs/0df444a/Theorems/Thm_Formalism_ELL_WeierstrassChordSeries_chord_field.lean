-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_chord_field
-- name    : Formalism.ELL.WeierstrassChordSeries.chord_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:26.312849+00:00
-- url     : https://prove2.me/theorems/de7a6073-50fa-47f2-a71b-49fa1f364905
-- title:
--   Weierstrass Chord Series: chord field
-- statement:
--   The Weierstrass Chord Series construction uses the chord field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L109-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L109-L172

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
variable {F : Type*} [Field F]

theorem Formalism.ELL.WeierstrassChordSeries.chord_field (a1 a2 a3 a4 a6 z1 z2 z3 v1 v2 v3 l n f u D : F)
    (hv1 : v1 = l * z1 + n) (hv2 : v2 = l * z2 + n) (hv3 : v3 = l * z3 + n)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0)
    (he2 : c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0)
    (he3 : c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0)
    (hc3 : c3 a2 a4 a6 l ≠ 0) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0) (hn : n ≠ 0)
    (hz : z1 ≠ z2) (hD : D = -1 + a1 * z3 + a3 * v3) (hD0 : D ≠ 0) (hf : f * D = z3)
    (hu : u * D = v3) :
    f / u = ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2 ∧
    -1 / u = -((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2) *
        ((((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2) - z1 / v1)
        + -1 / v1) - a1 * (((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2) - a3 := by sorry
