-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_gg_step
-- name    : Formalism.HermitianLatticeCounting.P.gg_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:39.096915+00:00
-- url     : https://prove2.me/theorems/cd2b9690-4954-4d61-89bb-507587d2bbe1
-- title:
--   P: gg step
-- statement:
--   The P construction uses the gg step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L199-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/IntegrableOnIoiTruncatedPowerMoment.lean#L199-L234

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

theorem Formalism.HermitianLatticeCounting.P.gg_step {d : ℕ} {R : Type*} [CommRing R] (Z : Matrix (Fin d) (Fin d) R) (q s : ℕ) (t : R)
    (hqs : q + s ≤ d)
    (h0 : ∀ i j : Fin d, q ≤ (i : ℕ) → (i : ℕ) < q + s → (j : ℕ) < q → Z i j = 0)
    (hD : ∀ i j : Fin d, q ≤ (i : ℕ) → (i : ℕ) < q + s → q ≤ (j : ℕ) → (j : ℕ) < q + s →
      Z i j = if (i : ℕ) + (j : ℕ) + 1 = 2 * q + s then t else 0) :
    leadingPrincipalMinor Z (q + s) = leadingPrincipalMinor Z q * ((-1) ^ (s.choose 2) * t ^ s) := by sorry
