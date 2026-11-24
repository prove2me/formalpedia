-- Prove2me | Theorems.Thm_Formalism_L2_SG_DensExact_prod_pairs
-- name    : Formalism.L2.SG.DensExact.prod_pairs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:30.365297+00:00
-- url     : https://prove2.me/theorems/7c20f844-8045-4fb2-9245-8f7de088fee5
-- title:
--   Dens Exact: prod pairs
-- statement:
--   The Dens Exact construction uses the prod pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/DensExact.lean#L54-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/DensExact.lean#L54-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.DensExact

theorem Formalism.L2.SG.DensExact.prod_pairs (f : ℕ → ℝ) : ∀ (c N : ℕ), 2 * c ≤ N →
    ∏ i ∈ range c, (f (N - 2 * i) * f (N - 2 * i - 1)) = ∏ j ∈ Ico (N + 1 - 2 * c) (N + 1), f j := by sorry
