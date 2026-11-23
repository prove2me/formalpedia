-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_low_divide
-- name    : Formalism.CyclotomicNorms.low_divide
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:36.198753+00:00
-- url     : https://prove2.me/theorems/42db12d9-8d41-49c4-8981-52839837c8fc
-- title:
--   Cyclotomic Norms: low divide
-- statement:
--   The Cyclotomic Norms construction uses the low divide property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/LowDegreePowerSeries.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/LowDegreePowerSeries.lean#L34-L39

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

theorem Formalism.CyclotomicNorms.low_divide {O : Type*} [CommRing O] (a : O) (f : PowerSeries O)
    (h : ∀ k, a ∣ coeff k f) : ∃ f', f = C a * f' := by sorry
