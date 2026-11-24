-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_summable_prod
-- name    : Formalism.HermitianLattices.Ext.L3.A5.summable_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:05.281992+00:00
-- url     : https://prove2.me/theorems/df8319d1-240d-4d11-8bd2-f12a93f4d53c
-- title:
--   A5: summable prod
-- statement:
--   The A5 construction uses the summable prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SummableSqGeom.lean#L63-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SummableSqGeom.lean#L63-L91

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

theorem Formalism.HermitianLattices.Ext.L3.A5.summable_prod {u : ι → ℕ → ℝ} (hu0 : ∀ i, u i 0 = 1) (hu : ∀ i j, 0 ≤ u i j) {t : ι → ℝ}
    (ht : Summable t) (hut : ∀ i J, ∑ j ∈ range (J + 1), u i j ≤ 1 + t i) :
    Summable fun v : ι →₀ ℕ => v.prod u := by sorry
