-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_sgF_apply
-- name    : Formalism.L2.Pj.FJ.sgF_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:46:15.958105+00:00
-- url     : https://prove2.me/theorems/49cebc79-a3db-45e8-a5f4-15cc0ee119bc
-- title:
--   FJ: sg F apply
-- statement:
--   The FJ construction uses the sg F apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L216-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean#L216-L221

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

theorem Formalism.L2.Pj.FJ.sgF_apply (X : Comp → Data E r) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ))
    (h : RdOrbInt σ X ρ rd) (cu : CuF X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) (f : C)
    {x : Frame (X cu.1).Ψ r} (hx : x ∈ (X cu.1).dom) :
    (sgF σ X rd h cu χ f : Frame (X cu.1).Ψ r → ℂ) x =
      coefFn (zAct (X cu.1) cu.2) (phZ (X cu.1) cu.2 χ) (rd f cu.1) x := by sorry
