-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gi_sesq_sum
-- name    : Formalism.HermitianLatticeCounting.P.gi_sesq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:44.173487+00:00
-- url     : https://prove2.me/theorems/034acd42-65ab-411b-aadd-f68681d31411
-- title:
--   P: gi sesq sum
-- statement:
--   The P construction uses the gi sesq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L564-L573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L564-L573

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
open scoped ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.gi_sesq_sum {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι] (h : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (c : ι → ℂ) (y : ι → V) :
    h (∑ a, c a • y a) (∑ b, c b • y b) = ∑ b, ∑ a, c a * conj (c b) * h (y a) (y b) := by sorry
