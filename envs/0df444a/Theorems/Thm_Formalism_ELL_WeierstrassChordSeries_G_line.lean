-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_G_line
-- name    : Formalism.ELL.WeierstrassChordSeries.G_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:55.573147+00:00
-- url     : https://prove2.me/theorems/12417169-bebb-471e-914d-9df42fafeb7b
-- title:
--   Weierstrass Chord Series: G line
-- statement:
--   The Weierstrass Chord Series construction uses the G line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L25-L29

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

theorem Formalism.ELL.WeierstrassChordSeries.G_line (a1 a2 a3 a4 a6 l n z : R) :
    G a1 a2 a3 a4 a6 z (l * z + n) = c3 a2 a4 a6 l * z ^ 3 + c2 a1 a2 a3 a4 a6 l n * z ^ 2
      + c1 a1 a3 a4 a6 l n * z + c0 a3 a6 n := by sorry
