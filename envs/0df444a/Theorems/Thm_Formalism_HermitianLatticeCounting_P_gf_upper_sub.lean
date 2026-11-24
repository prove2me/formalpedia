-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gf_upper_sub
-- name    : Formalism.HermitianLatticeCounting.P.gf_upper_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:23.439264+00:00
-- url     : https://prove2.me/theorems/ba968433-088d-4de6-b71f-4c7aaaa6be5b
-- title:
--   P: gf upper sub
-- statement:
--   The P construction uses the gf upper sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L323-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L323-L339

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

theorem Formalism.HermitianLatticeCounting.P.gf_upper_sub {R : Type*} [CommRing R] {d : ℕ} {α β β' : Type*} [Fintype α] (ρ : α → Fin d)
    (hinj : Function.Injective ρ) (hdown : ∀ a x, x ≤ ρ a → ∃ b, ρ b = x)
    (u : Matrix (Fin d) (Fin d) R) (hu : IsUpperUnitriangular u) (M : Matrix β (Fin d) R) (κ : β' → β) :
    (M * u).submatrix κ ρ = M.submatrix κ ρ * u.submatrix ρ ρ := by sorry
