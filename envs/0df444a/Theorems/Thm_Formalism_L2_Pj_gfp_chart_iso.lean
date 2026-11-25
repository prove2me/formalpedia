-- Prove2me | Theorems.Thm_Formalism_L2_Pj_gfp_chart_iso
-- name    : Formalism.L2.Pj.gfp_chart_iso
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:02:51.314826+00:00
-- url     : https://prove2.me/theorems/57f96e30-59ad-47d4-9ef7-4ed4f1752bf4
-- title:
--   Pj: gfp chart iso
-- statement:
--   The Pj construction uses the gfp chart iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenFrPfB.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenFrPfB.lean#L17-L33

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

theorem Formalism.L2.Pj.gfp_chart_iso {R : Type} [CommRing R] {G₁ G₂ : Over (Spec (CommRingCat.of R))} [GrpObj G₁] [GrpObj G₂]
    (e : G₁ ≅ G₂) [IsMonHom e.hom] {n : ℕ}
    {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (JetR R (Fin n) m) ⟶ G₁} (hx : IsUnivChart G₁ n xc) :
    IsUnivChart G₂ n (fun m => xc m ≫ e.hom) := by sorry
