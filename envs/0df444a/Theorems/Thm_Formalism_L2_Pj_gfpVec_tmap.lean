-- Prove2me | Theorems.Thm_Formalism_L2_Pj_gfpVec_tmap
-- name    : Formalism.L2.Pj.gfpVec_tmap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:03:00.751808+00:00
-- url     : https://prove2.me/theorems/7e2a4f39-fa4a-4bc1-afd6-7fe86544372b
-- title:
--   Pj: gfp Vec tmap
-- statement:
--   The Pj construction uses the gfp Vec tmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenFrPfB.lean#L45-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenFrPfB.lean#L45-L62

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfB
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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}

theorem Formalism.L2.Pj.gfpVec_tmap (hx : IsUnivChart _ n xc) (a : 𝓞 E) (cc : Fin n → L) :
    gfpVec x xc (tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)) cc) =
      gfpVec x xc cc ≫ (Xo.univ.t.act.act a).left := by sorry
