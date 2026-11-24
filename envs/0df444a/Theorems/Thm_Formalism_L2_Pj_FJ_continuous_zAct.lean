-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_continuous_zAct
-- name    : Formalism.L2.Pj.FJ.continuous_zAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:19.405965+00:00
-- url     : https://prove2.me/theorems/6047110b-ade1-4b1a-946b-ef30db449d6c
-- title:
--   FJ: continuous z Act
-- statement:
--   The FJ construction uses the continuous z Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L226-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L226-L229

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
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
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Pj
open Formalism.L2.Pj.FJ
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
variable {Comp : Type}
variable {K : Type} [Field K] (σ : K →+* ℂ)
variable {C : Type} [AddCommGroup C] [Module K C]

theorem Formalism.L2.Pj.FJ.continuous_zAct (X : Data E r) (cu : CuspFD X ρ) (x : Frame X.Ψ r) :
    Continuous fun t => zAct X cu t x := by sorry
