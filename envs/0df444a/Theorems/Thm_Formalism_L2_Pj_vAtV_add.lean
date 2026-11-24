-- Prove2me | Theorems.Thm_Formalism_L2_Pj_vAtV_add
-- name    : Formalism.L2.Pj.vAtV_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:05.446919+00:00
-- url     : https://prove2.me/theorems/7c4f49b8-ce1b-4690-8f7e-aecc4f080f70
-- title:
--   Pj: v At V add
-- statement:
--   The Pj construction uses the v At V add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/VAtVNeBot.lean#L148-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/VAtVNeBot.lean#L148-L152

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
variable (Xo c)
variable {Xo c}
variable (Xo c)
variable (cls : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) (PY : Type)
  (lies : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → PY → Prop)
variable {Xo c cls PY lies}
variable {la : HeightOneSpectrum (𝓞 c.F)}

theorem Formalism.L2.Pj.vAtV_add (y : PtV Xo c cls PY lies la) (f g : Rul Xo c) :
    min (vAtV y f) (vAtV y g) ≤ vAtV y (f + g) := by sorry
