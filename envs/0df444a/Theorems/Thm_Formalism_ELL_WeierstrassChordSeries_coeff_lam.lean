-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_lam
-- name    : Formalism.ELL.WeierstrassChordSeries.coeff_lam
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:21.767624+00:00
-- url     : https://prove2.me/theorems/a4dc1197-4629-4b63-b6ba-cf7caef98bf6
-- title:
--   Weierstrass Chord Series: coeff lam
-- statement:
--   The Weierstrass Chord Series construction uses the coeff lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L296-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L296-L297

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

theorem Formalism.ELL.WeierstrassChordSeries.coeff_lam (w : PowerSeries K) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam w) = coeff (e 0 + e 1 + 1) w := by sorry
