-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_der_aeval
-- name    : Formalism.L2.Pj.GenericSectionMinimum.der_aeval
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:47:18.411744+00:00
-- url     : https://prove2.me/theorems/76f4fb91-49f4-40ae-a2cb-f1679b244c85
-- title:
--   Generic Section Minimum: der aeval
-- statement:
--   The Generic Section Minimum construction uses the der aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L45-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L45-L67

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt
import Theorems.Thm_UpperTheory_Reformulated_B_Qf29_der_aeval

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
variable {F : Type} [Field F]

theorem Formalism.L2.Pj.GenericSectionMinimum.der_aeval {δ : F → F} (h : IsDer δ) {E : Type} [CommRing E] [Algebra E F]
    (hE : ∀ e, δ (algebraMap E F e) = 0) {σ : Type} [Fintype σ] [DecidableEq σ] (t : σ → F)
    (P : MvPolynomial σ E) :
    δ (MvPolynomial.aeval t P) = ∑ i, MvPolynomial.aeval t (MvPolynomial.pderiv i P) * δ (t i) := by sorry
