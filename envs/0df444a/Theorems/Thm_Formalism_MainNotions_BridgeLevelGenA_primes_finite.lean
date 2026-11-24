-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelGenA_primes_finite
-- name    : Formalism.MainNotions.BridgeLevelGenA.primes_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:58.126592+00:00
-- url     : https://prove2.me/theorems/ae4095c4-ba9a-49fa-8147-422cd1bf139a
-- title:
--   Bridge Level Gen A: primes finite
-- statement:
--   The Bridge Level Gen A construction uses the primes finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGenA.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGenA.lean#L38-L49

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenA
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem Formalism.MainNotions.BridgeLevelGenA.primes_finite (g : R) (hg : g ≠ 0) :
    {P : Ideal R | P.IsPrime ∧ Disjoint (coprS g : Set R) (P : Set R)}.Finite := by sorry
