-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_ordGe_aeval_monomial
-- name    : Formalism.L2.Pj.Crude.ordGe_aeval_monomial
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:47:19.817011+00:00
-- url     : https://prove2.me/theorems/01dc2b9c-394a-4ad4-b89e-42a99b7a9c3e
-- title:
--   Crude: ord Ge aeval monomial
-- statement:
--   The Crude construction uses the ord Ge aeval monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L61-L74

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}

theorem Formalism.L2.Pj.Crude.ordGe_aeval_monomial {ι : Type} (φ : ι → PS k n d) (hφ : ∀ i, OrdGe 1 (φ i)) (α : ι →₀ ℕ) :
    OrdGe α.degree (MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : k))) := by sorry
