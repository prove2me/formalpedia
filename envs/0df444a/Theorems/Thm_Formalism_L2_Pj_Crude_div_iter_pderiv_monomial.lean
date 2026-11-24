-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_div_iter_pderiv_monomial
-- name    : Formalism.L2.Pj.Crude.div_iter_pderiv_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:06.094706+00:00
-- url     : https://prove2.me/theorems/416d0e24-4d5a-40b8-b0c9-ab085a114c9b
-- title:
--   Crude: div iter pderiv monomial
-- statement:
--   The Crude construction uses the div iter pderiv monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L126-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L126-L146

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

theorem Formalism.L2.Pj.Crude.div_iter_pderiv_monomial {ι : Type} [DecidableEq ι] (i : ι) (t : ℕ) (s : ι →₀ ℕ) (c : k) :
    (MvPolynomial.pderiv i)^[t] (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - Finsupp.single i t) (c * ((s i).descFactorial t : k)) := by sorry
