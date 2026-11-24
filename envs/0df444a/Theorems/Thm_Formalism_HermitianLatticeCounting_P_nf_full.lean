-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_nf_full
-- name    : Formalism.HermitianLatticeCounting.P.nf_full
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:21.986794+00:00
-- url     : https://prove2.me/theorems/86c9c867-b2f5-46a8-af6d-a4bf9560a1d9
-- title:
--   P: nf full
-- statement:
--   The P construction uses the nf full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1392-L1419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExistsHasLeadingCoeffOfMemSpanBelow.lean#L1392-L1419

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.nf_full {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {H : HermSpace K V} {r : ℕ} (F F' : FlagD H r) (hA : F.Aniso) (hA' : F'.Aniso) (j : ℕ) (hj : j ≤ r)
    (c : K) (hS : NFShape F F' j c) : NFFull F F' j hj c := by sorry
