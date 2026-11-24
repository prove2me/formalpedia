-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_div_constCoeff_aeval
-- name    : Formalism.L2.Pj.Crude.div_constCoeff_aeval
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:53.313941+00:00
-- url     : https://prove2.me/theorems/514e06f2-8068-4469-b7a8-50d0c4ba954b
-- title:
--   Crude: div const Coeff aeval
-- statement:
--   The Crude construction uses the div const Coeff aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L119-L124

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

theorem Formalism.L2.Pj.Crude.div_constCoeff_aeval {ι : Type} (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (Q : MvPolynomial ι k) : constantCoeff (MvPolynomial.aeval φ Q) = MvPolynomial.constantCoeff Q := by sorry
