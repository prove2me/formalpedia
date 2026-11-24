-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_skew_beta
-- name    : Formalism.L2.Pj.FJ.skew_beta
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:09.5389+00:00
-- url     : https://prove2.me/theorems/1e4529ee-35e4-4f6d-a3e7-f08e41f5ce88
-- title:
--   FJ: skew beta
-- statement:
--   The FJ construction uses the skew beta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L120-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean#L120-L127

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

theorem Formalism.L2.Pj.FJ.skew_beta (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k)) (τ : E →+* ℂ)
    (t : Fin (nZ X ρ) → ℝ) :
    cM (∑ k, (t k : ℂ) • (zBas X cu k).map τ) = -(∑ k, (t k : ℂ) • (zBas X cu k).map τ)ᵀ := by sorry
