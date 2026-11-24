-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_word
-- name    : Formalism.L2.Pj.Crude.cro_word
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:14.043574+00:00
-- url     : https://prove2.me/theorems/7fbafbca-3db6-496d-93a2-8de528120b87
-- title:
--   Crude: cro word
-- statement:
--   The Crude construction uses the cro word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L261-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L261-L285

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

theorem Formalism.L2.Pj.Crude.cro_word {ι : Type} (Op Op' : ι → PS k n d → PS k n d) (m : ι →₀ ℕ)
    (hsub : ∀ l X Y, Op l (X - Y) = Op l X - Op l Y)
    (hlow : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op l X)) (hlow' : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op' l X))
    (hdiff : ∀ l t X, OrdGe (t + 1) X → OrdGe (t + 1) (Op l X - Op' l X)) (L : List ι) :
    ∀ (s : ℕ) (X Y : PS k n d), OrdGe ((L.map m).sum + s) X → OrdGe ((L.map m).sum + s) Y →
      OrdGe ((L.map m).sum + s + 1) (X - Y) →
      OrdGe s (L.foldr (fun l g => (Op l)^[m l] g) X) ∧ OrdGe s (L.foldr (fun l g => (Op' l)^[m l] g) Y) ∧
      OrdGe (s + 1) (L.foldr (fun l g => (Op l)^[m l] g) X - L.foldr (fun l g => (Op' l)^[m l] g) Y) := by sorry
