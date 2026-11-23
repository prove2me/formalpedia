-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassSeriesLimit_seq_far
-- name    : Formalism.ELL.WeierstrassSeriesLimit.seq_far
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:17.959389+00:00
-- url     : https://prove2.me/theorems/cce6db7b-00b8-429f-a95c-149d1659b8bd
-- title:
--   Weierstrass Series Limit: seq far
-- statement:
--   The Weierstrass Series Limit construction uses the seq far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L70-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean#L70-L79

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
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
open Formalism.ELL.WeierstrassSeriesLimit
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem Formalism.ELL.WeierstrassSeriesLimit.seq_far (j i : ℕ) : X ^ j ∣ seq W (j + i) - seq W j := by sorry
