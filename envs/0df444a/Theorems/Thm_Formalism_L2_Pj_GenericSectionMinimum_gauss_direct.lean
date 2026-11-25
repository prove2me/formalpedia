-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_gauss_direct
-- name    : Formalism.L2.Pj.GenericSectionMinimum.gauss_direct
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:36:03.019134+00:00
-- url     : https://prove2.me/theorems/3bf297e7-9884-4ab4-a397-fae8b0cc4dcc
-- title:
--   Generic Section Minimum: gauss direct
-- statement:
--   The Generic Section Minimum construction uses the gauss direct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L224-L445
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L224-L445

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt
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

theorem Formalism.L2.Pj.GenericSectionMinimum.gauss_direct {F K : Type} [Field F] [Field K] [CharZero K] [Algebra K F] (D N : ℕ)
    (T : Fin (D + 1) × Fin N → F) (y : Fin N → F) (δ : Fin N → F → F) (hδ : ∀ l, IsDer (δ l))
    (hδK : ∀ l c, δ l (algebraMap K F c) = 0) (hδ0 : ∀ l k, δ l (T (0, k)) = if k = l then 1 else 0)
    (hδs : ∀ l (i : Fin D) k, δ l (T (i.succ, k)) = 0) (hδy : ∀ l k, δ l (y k) = -(y k * y l))
    (h1 : ∑ k, T (0, k) * y k = 1)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range T)) F)
    (V : ValuationSubring F)
    (hG : ∀ Q : MvPolynomial (Fin (D + 1) × Fin N) K, (∀ α, V.valuation (algebraMap K F (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap K F (Q.coeff α)) = 1) → V.valuation (MvPolynomial.aeval T Q) = 1) :
    ∀ k, y k ∈ V := by sorry
