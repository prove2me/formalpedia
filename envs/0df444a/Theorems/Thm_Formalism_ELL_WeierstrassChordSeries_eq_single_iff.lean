-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_eq_single_iff
-- name    : Formalism.ELL.WeierstrassChordSeries.eq_single_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:55.728475+00:00
-- url     : https://prove2.me/theorems/0f03c8d4-a24c-4e41-a9a3-d47f569ac434
-- title:
--   Weierstrass Chord Series: eq single iff
-- statement:
--   The Weierstrass Chord Series construction uses the eq single iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L282-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L282-L292

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

theorem Formalism.ELL.WeierstrassChordSeries.eq_single_iff (e : Fin 2 →₀ ℕ) :
    (e = Finsupp.single 1 (e 1) ↔ e 0 = 0) ∧ (e = Finsupp.single 0 (e 0) ↔ e 1 = 0) := by sorry
