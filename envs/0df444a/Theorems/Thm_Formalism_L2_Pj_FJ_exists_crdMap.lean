-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FJ_exists_crdMap
-- name    : Formalism.L2.Pj.FJ.exists_crdMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:32:35.156261+00:00
-- url     : https://prove2.me/theorems/e3722df5-bad9-4903-84cb-4591ea00e443
-- title:
--   FJ: exists crd Map
-- statement:
--   The FJ construction uses the exists crd Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L73-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SpanRatSmulMem.lean#L73-L88

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LocalSituation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SpanRatSmulMem
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
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem Formalism.L2.Pj.FJ.exists_crdMap {X : Data E r} (cu : CuspFD X ρ) :
    ∃ Ψ : (Fin r → E) →ₗ[E] (Fin ρ → E), ∀ v : Fin ρ → E, Ψ (∑ i, v i • cu.e i) = v := by sorry
