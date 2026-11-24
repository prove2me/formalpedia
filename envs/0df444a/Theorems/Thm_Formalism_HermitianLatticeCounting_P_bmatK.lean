-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_bmatK
-- name    : Formalism.HermitianLatticeCounting.P.bmatK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:40.52223+00:00
-- url     : https://prove2.me/theorems/cf4946f2-4789-4e62-97ca-0a487ef83d34
-- title:
--   P: bmat K
-- statement:
--   The P construction uses the bmat K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L458-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MinkowskiNumberDvdFactorial.lean#L458-L465

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
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
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]

theorem Formalism.HermitianLatticeCounting.P.bmatK (h' : U →ₗ[K] U →ₗ⋆[K] K) {m : ℕ} (e f : Fin m → U) (A C : Matrix (Fin m) (Fin m) K)
    (u w : Fin m → U) (hu : ∀ i, u i = ∑ k, A i k • e k) (hw : ∀ j, w j = ∑ l, C j l • f l) :
    (Matrix.of fun i j => h' (u i) (w j)) = A * (Matrix.of fun k l => h' (e k) (f l)) * Cᴴ := by sorry
