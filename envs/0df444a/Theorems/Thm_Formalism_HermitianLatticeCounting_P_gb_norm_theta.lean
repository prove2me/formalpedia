-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gb_norm_theta
-- name    : Formalism.HermitianLatticeCounting.P.gb_norm_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:22.659585+00:00
-- url     : https://prove2.me/theorems/477ef532-1bb3-46e9-b654-43e4f0c84214
-- title:
--   P: gb norm theta
-- statement:
--   The P construction uses the gb norm theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L784-L790
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L784-L790

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset
open scoped ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.gb_norm_theta {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {θ : V →ₗ[ℂ] V}
    (h : IsSelfAdjointInvolution θ) (x : V) : ‖θ x‖ = ‖x‖ := by sorry
