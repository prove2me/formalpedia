-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_low_key
-- name    : Formalism.CyclotomicNorms.low_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:58.555024+00:00
-- url     : https://prove2.me/theorems/fa516247-bc6a-4c1f-885b-7fc7e23b5772
-- title:
--   Cyclotomic Norms: low key
-- statement:
--   The Cyclotomic Norms construction uses the low key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/LowDegreePowerSeries.lean#L9-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/LowDegreePowerSeries.lean#L9-L25

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_LowDegreePowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.CyclotomicNorms

theorem Formalism.CyclotomicNorms.low_key {R : Type*} [CommRing R] (x p D' y : R) (U : Rˣ) (m n : ℕ)
    (hp : p ^ n = 0) (hD : (x ^ m * U + p * D') * y = 0) : x ^ (m * n) * y = 0 := by sorry
