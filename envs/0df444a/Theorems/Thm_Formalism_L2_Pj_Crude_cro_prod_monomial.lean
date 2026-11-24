-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_prod_monomial
-- name    : Formalism.L2.Pj.Crude.cro_prod_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:05.003776+00:00
-- url     : https://prove2.me/theorems/286342ca-ba37-4a33-9919-7c4c668b6306
-- title:
--   Crude: cro prod monomial
-- statement:
--   The Crude construction uses the cro prod monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L127-L136

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}

theorem Formalism.L2.Pj.Crude.cro_prod_monomial {ι σ : Type} (s : Finset ι) (f : ι → σ →₀ ℕ) :
    ∏ i ∈ s, (monomial (f i) (1 : k) : MvPowerSeries σ k) = monomial (∑ i ∈ s, f i) 1 := by sorry
