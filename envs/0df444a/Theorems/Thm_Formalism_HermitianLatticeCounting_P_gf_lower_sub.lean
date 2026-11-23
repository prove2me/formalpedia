-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_lower_sub
-- name    : Formalism.HermitianLatticeCounting.P.gf_lower_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:03:35.758873+00:00
-- url     : https://prove2.me/theorems/75416ccc-a509-4981-bab2-2c2c1f4f4911
-- title:
--   P: gf lower sub
-- statement:
--   The P construction uses the gf lower sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L305-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L305-L321

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

theorem Formalism.HermitianLatticeCounting.P.gf_lower_sub {R : Type*} [CommRing R] {d : ℕ} {α β β' : Type*} [Fintype α] (ρ : α → Fin d)
    (hinj : Function.Injective ρ) (hdown : ∀ a x, x ≤ ρ a → ∃ b, ρ b = x)
    (l : Matrix (Fin d) (Fin d) R) (hl : IsLowerUnitriangular l) (M : Matrix (Fin d) β R) (κ : β' → β) :
    (l * M).submatrix ρ κ = l.submatrix ρ ρ * M.submatrix ρ κ := by sorry
