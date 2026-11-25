-- Prove2me | Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_gauss_indep
-- name    : Formalism.L2.Pj.GenericSectionMinimum.gauss_indep
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:36:48.341455+00:00
-- url     : https://prove2.me/theorems/bed4d4ca-0e18-4f30-9db3-514f670ea91f
-- title:
--   Generic Section Minimum: gauss indep
-- statement:
--   The Generic Section Minimum construction uses the gauss indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L137-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/TotalDegreePderivLt.lean#L137-L222

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

theorem Formalism.L2.Pj.GenericSectionMinimum.gauss_indep {K Ω U τ : Type} [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U] [Algebra K U]
    [IsScalarTower K Ω U] (V : ValuationSubring U) (T : τ → U) (hT : ∀ q, T q ∈ V)
    (hG : ∀ Q : MvPolynomial τ K, (∀ α, V.valuation (algebraMap K U (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap K U (Q.coeff α)) = 1) → V.valuation (MvPolynomial.aeval T Q) = 1) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
    letI : Algebra (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V) :=
      ((algebraMap _ (ResidueField V)).comp (algebraMap _ (ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => residue V ⟨T j, hT j⟩) := by sorry
