-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_zBas_skew
-- name    : Formalism.L2.Pj.FJ.zBas_skew
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:40.011348+00:00
-- url     : https://prove2.me/theorems/c48266b0-52ea-4a21-89d1-083520614dba
-- title:
--   FJ: z Bas skew
-- statement:
--   The FJ construction uses the z Bas skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L129-L134

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem Formalism.L2.Pj.FJ.zBas_skew (X : Data E r) (cu : CuspFD X ρ) (h : ∃ bs, IsZBasis X cu bs) (k : Fin (nZ X ρ)) :
    IsSkew (zBas X cu k) := by sorry
