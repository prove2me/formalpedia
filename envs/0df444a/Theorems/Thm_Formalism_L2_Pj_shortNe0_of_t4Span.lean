-- Prove2me | Theorems.Thm_Formalism_L2_Pj_shortNe0_of_t4Span
-- name    : Formalism.L2.Pj.shortNe0_of_t4Span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:46:26.081616+00:00
-- url     : https://prove2.me/theorems/d9c9bd64-e3fb-4d00-8ef4-b5d5d1670a43
-- title:
--   Pj: short Ne0 of t4 Span
-- statement:
--   The Pj construction uses the short Ne0 of t4 Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ThShort.lean#L335-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ThShort.lean#L335-L348

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open MvPolynomial
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem Formalism.L2.Pj.shortNe0_of_t4Span (nab : NabV Xo c) (bad nV : ℕ) (dδ : ∀ n, DeltaDat Xo c n)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
    (h : SpanningAtDominantWeight Xo c nab bad nV cusp dδ) : ShortNe0 Xo c nab bad nV dδ cusp := by sorry
