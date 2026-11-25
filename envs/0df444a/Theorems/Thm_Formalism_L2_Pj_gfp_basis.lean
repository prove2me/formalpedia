-- Prove2me | Theorems.Thm_Formalism_L2_Pj_gfp_basis
-- name    : Formalism.L2.Pj.gfp_basis
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:14:45.376265+00:00
-- url     : https://prove2.me/theorems/61585599-425a-474a-9324-16b882552227
-- title:
--   Pj: gfp basis
-- statement:
--   The Pj construction uses the gfp basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenFrPfB.lean#L131-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenFrPfB.lean#L131-L158

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
variable [Algebra c.F L]

theorem Formalism.L2.Pj.gfp_basis (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ)
    (d : Fin (Dw.mult τ) → Fin n → L) (hd : LinearIndependent L d) (hdW : ∀ i, d i ∈ gfpEig (c := c) hx τ)
    (w : Sp (DualNumber L) ⟶ Xo.univ.t.G.left) (hw : IsTanAt x w) (he : IsEigAt c τ w) :
    ∃! a : Fin (Dw.mult τ) → L, IsCombAt x (fun i => gfpVec x xc (d i)) a w := by sorry
