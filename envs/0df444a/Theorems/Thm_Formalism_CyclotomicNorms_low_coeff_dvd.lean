-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_low_coeff_dvd
-- name    : Formalism.CyclotomicNorms.low_coeff_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:56:36.666804+00:00
-- url     : https://prove2.me/theorems/0e37b756-fd5e-42c2-83a6-a30677fc77e2
-- title:
--   Cyclotomic Norms: low coeff dvd
-- statement:
--   The Cyclotomic Norms construction uses the low coeff dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/LowDegreePowerSeries.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/LowDegreePowerSeries.lean#L27-L32

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

theorem Formalism.CyclotomicNorms.low_coeff_dvd {O : Type*} [CommRing O] (a : O) (M : ℕ) (f : PowerSeries O)
    (hf : f ∈ Ideal.span {PowerSeries.C a, (PowerSeries.X : PowerSeries O) ^ (M + 1)})
    (k : ℕ) (hk : k ≤ M) : a ∣ coeff k f := by sorry
