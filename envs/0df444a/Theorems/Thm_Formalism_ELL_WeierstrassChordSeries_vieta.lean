-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_vieta
-- name    : Formalism.ELL.WeierstrassChordSeries.vieta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:18.62677+00:00
-- url     : https://prove2.me/theorems/2b609c33-f5d6-49d6-ad31-97cc08eff97a
-- title:
--   Weierstrass Chord Series: vieta
-- statement:
--   The Weierstrass Chord Series construction uses the vieta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L31-L50

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

theorem Formalism.ELL.WeierstrassChordSeries.vieta [IsDomain R] {a1 a2 a3 a4 a6 l n z1 z2 z3 : R} (hz : z1 ≠ z2)
    (h1 : G a1 a2 a3 a4 a6 z1 (l * z1 + n) = 0) (h2 : G a1 a2 a3 a4 a6 z2 (l * z2 + n) = 0)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0) :
    G a1 a2 a3 a4 a6 z3 (l * z3 + n) = 0 ∧
      c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0 ∧
      c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0 := by sorry
