-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_summable_dif
-- name    : Formalism.HermitianLattices.Ext.L3.A5.summable_dif
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:33.164479+00:00
-- url     : https://prove2.me/theorems/8fecc17a-90d0-4e31-9d30-5ab8312fb93d
-- title:
--   A5: summable dif
-- statement:
--   The A5 construction uses the summable dif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SummableSqGeom.lean#L162-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SummableSqGeom.lean#L162-L168

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {ι : Type*}
variable {q : ι → ℝ}

theorem Formalism.HermitianLattices.Ext.L3.A5.summable_dif (hq : ∀ i, 2 ≤ q i) (hsum : Summable fun i => (q i ^ 2)⁻¹) {R : ι → ℕ → ℝ}
    (hRb : ∀ i j, |R i (j + 1) - R i j| ≤ 8 * ((j : ℝ) + 2) ^ 2 / q i) :
    Summable fun v : ι →₀ ℕ => |v.prod (dif R)| / nrm q v := by sorry
