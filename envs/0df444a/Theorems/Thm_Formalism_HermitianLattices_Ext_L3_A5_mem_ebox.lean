-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_mem_ebox
-- name    : Formalism.HermitianLattices.Ext.L3.A5.mem_ebox
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:31.011972+00:00
-- url     : https://prove2.me/theorems/abbed356-e852-42c4-a451-6928e2f4dfcd
-- title:
--   A5: mem ebox
-- statement:
--   The A5 construction uses the mem ebox property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SummableSqGeom.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SummableSqGeom.lean#L13-L16

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

theorem Formalism.HermitianLattices.Ext.L3.A5.mem_ebox {s : Finset ι} {J : ι → ℕ} {v : ι →₀ ℕ} :
    v ∈ ebox s J ↔ v.support ⊆ s ∧ ∀ i ∈ s, v i ≤ J i := by sorry
