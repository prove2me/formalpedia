-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_iter
-- name    : Formalism.L2.Pj.Crude.cro_iter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:37.11598+00:00
-- url     : https://prove2.me/theorems/c40fbe90-20b5-4020-9ba9-7836da250745
-- title:
--   Crude: cro iter
-- statement:
--   The Crude construction uses the cro iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L233-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L233-L257

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
variable (Op Op' : PS k n d → PS k n d)

theorem Formalism.L2.Pj.Crude.cro_iter (hsub : ∀ X Y, Op (X - Y) = Op X - Op Y)
    (hlow : ∀ t X, OrdGe (t + 1) X → OrdGe t (Op X)) (hlow' : ∀ t X, OrdGe (t + 1) X → OrdGe t (Op' X))
    (hdiff : ∀ t X, OrdGe (t + 1) X → OrdGe (t + 1) (Op X - Op' X)) (c : ℕ) :
    ∀ (s : ℕ) (X Y : PS k n d), OrdGe (c + s) X → OrdGe (c + s) Y → OrdGe (c + s + 1) (X - Y) →
      OrdGe s (Op^[c] X) ∧ OrdGe s (Op'^[c] Y) ∧ OrdGe (s + 1) (Op^[c] X - Op'^[c] Y) := by sorry
