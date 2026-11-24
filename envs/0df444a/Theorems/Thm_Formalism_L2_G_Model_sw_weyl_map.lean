-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_sw_weyl_map
-- name    : Formalism.L2.G.Model.sw_weyl_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:45.887509+00:00
-- url     : https://prove2.me/theorems/369db93c-0d63-4076-9033-6462777096ff
-- title:
--   Model: sw weyl map
-- statement:
--   The Model construction uses the sw weyl map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowGenMonomial.lean#L162-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowGenMonomial.lean#L162-L175

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility

theorem Formalism.L2.G.Model.sw_weyl_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) :
    map φ f ∈ weyl S r n hn ν := by sorry
