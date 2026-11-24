-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_prod_dif_cut
-- name    : Formalism.HermitianLattices.Ext.L3.A5.prod_dif_cut
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:04.479238+00:00
-- url     : https://prove2.me/theorems/a0194563-577a-4c27-a5b9-818c4fb5b8ee
-- title:
--   A5: prod dif cut
-- statement:
--   The A5 construction uses the prod dif cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L124-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L124-L141

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

theorem Formalism.HermitianLattices.Ext.L3.A5.prod_dif_cut (ρ : ι → ℕ → ℝ) (S' : Finset ι) (v : ι →₀ ℕ) :
    v.prod (dif (cut ρ S')) = if v.support ⊆ S' then v.prod (dif ρ) else 0 := by sorry
