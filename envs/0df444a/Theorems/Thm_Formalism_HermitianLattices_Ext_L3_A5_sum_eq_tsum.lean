-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_sum_eq_tsum
-- name    : Formalism.HermitianLattices.Ext.L3.A5.sum_eq_tsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:18.647839+00:00
-- url     : https://prove2.me/theorems/79dc6fb6-8d04-478b-9d7c-931a9acb55ba
-- title:
--   A5: sum eq tsum
-- statement:
--   The A5 construction uses the sum eq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L21-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L21-L58

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoWeightedTprod
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
variable {ι X : Type*} {q : ι → ℝ}
open scoped Classical

theorem Formalism.HermitianLattices.Ext.L3.A5.sum_eq_tsum {R : ι → ℕ → ℝ} (hR0 : ∀ i, R i 0 = 1) (val : X → ι →₀ ℕ) (B : Finset X)
    (a : X → ℝ) (sc : ℝ) :
    sc * ∑ n ∈ B, a n * (val n).prod R =
      ∑' v : ι →₀ ℕ, v.prod (dif R) * (sc * ∑ n ∈ B.filter (fun n => v ≤ val n), a n) := by sorry
