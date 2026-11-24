-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gj_cols
-- name    : Formalism.HermitianLatticeCounting.P.gj_cols
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:26.022752+00:00
-- url     : https://prove2.me/theorems/ce50884f-a256-4caf-8238-035e02524606
-- title:
--   P: gj cols
-- statement:
--   The P construction uses the gj cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L657-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L657-L673

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Matrix Finset

theorem Formalism.HermitianLatticeCounting.P.gj_cols {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin n) ℂ) :
    s * F = F * U ↔ ∀ b, s *ᵥ (fun i => F i b) = ∑ e, U e b • (fun i => F i e) := by sorry
