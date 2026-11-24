-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_word_const
-- name    : Formalism.L2.Pj.Crude.cro_word_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:00.965391+00:00
-- url     : https://prove2.me/theorems/86b765f6-1c9b-4fb2-ba9c-4577313373f6
-- title:
--   Crude: cro word const
-- statement:
--   The Crude construction uses the cro word const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L287-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L287-L311

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

theorem Formalism.L2.Pj.Crude.cro_word_const {ι : Type} [Fintype ι] (Op Op' : ι → PS k n d → PS k n d) (m : ι →₀ ℕ)
    (hsub : ∀ l X Y, Op l (X - Y) = Op l X - Op l Y)
    (hlow : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op l X)) (hlow' : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op' l X))
    (hdiff : ∀ l t X, OrdGe (t + 1) X → OrdGe (t + 1) (Op l X - Op' l X)) (X Y : PS k n d)
    (hX : OrdGe m.degree X) (hY : OrdGe m.degree Y) (hXY : OrdGe (m.degree + 1) (X - Y)) :
    constantCoeff ((Finset.univ : Finset ι).toList.foldr (fun l g => (Op l)^[m l] g) X) =
      constantCoeff ((Finset.univ : Finset ι).toList.foldr (fun l g => (Op' l)^[m l] g) Y) := by sorry
