-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_prod_cut
-- name    : Formalism.HermitianLattices.Ext.L3.A5.prod_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:04.265523+00:00
-- url     : https://prove2.me/theorems/c72aa39a-7890-487b-8c80-24fe18cdaaba
-- title:
--   A5: prod cut
-- statement:
--   The A5 construction uses the prod cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L111-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoWeightedTprod.lean#L111-L121

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

theorem Formalism.HermitianLattices.Ext.L3.A5.prod_cut {ρ : ι → ℕ → ℝ} (hρ0 : ∀ i, ρ i 0 = 1) (S' : Finset ι) (w : ι →₀ ℕ) :
    w.prod (cut ρ S') = ∏ i ∈ S', ρ i (w i) := by sorry
