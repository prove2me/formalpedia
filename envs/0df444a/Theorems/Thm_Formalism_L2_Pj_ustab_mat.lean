-- Prove2me | Theorems.Thm_Formalism_L2_Pj_ustab_mat
-- name    : Formalism.L2.Pj.ustab_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:03.707626+00:00
-- url     : https://prove2.me/theorems/d7c6b519-65be-4a4f-a8ab-c429c2a1f633
-- title:
--   Pj: ustab mat
-- statement:
--   The Pj construction uses the ustab mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L100-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnifDom.lean#L100-L117

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem Formalism.L2.Pj.ustab_mat {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} {γ : GL (Fin r) E}
    (h : IsUStab G Λ γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by sorry
