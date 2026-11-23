-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_pt_mul_pt
-- name    : Formalism.DoubleCosetMeasures.P.Supp.pt_mul_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:26.890209+00:00
-- url     : https://prove2.me/theorems/920926a9-2822-4eaa-a4c4-033ad43de94e
-- title:
--   Supp: pt mul pt
-- statement:
--   The Supp construction uses the pt mul pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L159-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/ExistsContinuousLowerUpperEntry.lean#L159-L175

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp

theorem Formalism.DoubleCosetMeasures.P.Supp.pt_mul_pt {K : Type} [CommRing K] (s : List ℕ) (t t' : ℕ → Kˣ)
    (htt : ∀ b, ((t b : Kˣ) : K) * ((t' b : Kˣ) : K) = 1) : pt s t * pt s t' = 1 := by sorry
