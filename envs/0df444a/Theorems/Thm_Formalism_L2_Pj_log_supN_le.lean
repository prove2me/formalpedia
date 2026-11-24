-- Prove2me | Theorems.Thm_Formalism_L2_Pj_log_supN_le
-- name    : Formalism.L2.Pj.log_supN_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:20:16.30731+00:00
-- url     : https://prove2.me/theorems/9a7a9078-6f08-46f6-b53d-fa4aa36c1332
-- title:
--   Pj: log sup N le
-- statement:
--   The Pj construction uses the log sup N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AxHSup.lean#L69-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AxHSup.lean#L69-L98

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

theorem Formalism.L2.Pj.log_supN_le (hfn : FnNe Xo c fn) (hPT : PTNe Xo c) (hcx : ValAtCx h yP) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f) (hN : NZSome h f) (σ : c.F →+* ℂ) :
    Real.log (⨆ p : (Σ Z : Comp Xo c, PT (Ω := Om Z) σ), nrmC fn (yP p.1) (wtZ a n) (valC h a n f p.1) p.2) ≤
      Real.log (supR Xo c fn σ a n f) := by sorry
