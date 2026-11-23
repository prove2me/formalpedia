-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_Wi
-- name    : Formalism.ELL.WeierstrassChordSeries.coeff_Wi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:23.756057+00:00
-- url     : https://prove2.me/theorems/c5372329-899c-4ef1-aab0-0d0f09ea8098
-- title:
--   Weierstrass Chord Series: coeff Wi
-- statement:
--   The Weierstrass Chord Series construction uses the coeff Wi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L301-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L301-L328

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
variable {K : Type u} [Field K]

theorem Formalism.ELL.WeierstrassChordSeries.coeff_Wi (w : PowerSeries K) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (Wi w i) = if e = Finsupp.single i (e i) then coeff (e i) w else 0 := by sorry
