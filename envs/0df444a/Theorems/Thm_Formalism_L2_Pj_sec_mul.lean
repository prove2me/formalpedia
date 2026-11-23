-- Prove2me | Theorems.Thm_Formalism_L2_Pj_sec_mul
-- name    : Formalism.L2.Pj.sec_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:36.268533+00:00
-- url     : https://prove2.me/theorems/44bd8733-8335-4dbe-961c-a0af5bb41832
-- title:
--   Pj: sec mul
-- statement:
--   The Pj construction uses the sec mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsCombAt.lean#L106-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IsCombAt.lean#L106-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
variable (Xo c)
variable {Xo c}
variable (Xo c)

theorem Formalism.L2.Pj.sec_mul (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : f * g ∈ sec Xo c (a + a') (n + n') := by sorry
