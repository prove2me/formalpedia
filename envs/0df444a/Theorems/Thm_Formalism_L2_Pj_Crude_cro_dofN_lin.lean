-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_dofN_lin
-- name    : Formalism.L2.Pj.Crude.cro_dofN_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:33.945802+00:00
-- url     : https://prove2.me/theorems/1a7b7d57-8198-4816-9cdd-3eb6575b53e4
-- title:
--   Crude: cro dof N lin
-- statement:
--   The Crude construction uses the cro dof N lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L327-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L327-L363

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

theorem Formalism.L2.Pj.Crude.cro_dofN_lin (F : Fin d → PS k 2 d)
    (hF : ∀ i j, coeff (Finsupp.single ((1 : Fin 2), i) 1) (F j) = if i = j then 1 else 0)
    (b : Fin n) (v : Fin d → k) {t : ℕ} {X : PS k n d} (hX : OrdGe (t + 1) X) :
    OrdGe (t + 1) (DofN F b v X - Lin b v X) := by sorry
