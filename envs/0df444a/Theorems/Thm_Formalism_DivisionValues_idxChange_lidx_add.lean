-- Prove2me | Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_add
-- name    : Formalism.DivisionValues.idxChange_lidx_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:23.132582+00:00
-- url     : https://prove2.me/theorems/884509c1-a74b-48ab-bb42-64a9e2e521e4
-- title:
--   Division Values: idx Change lidx add
-- statement:
--   The Division Values construction uses the idx Change lidx add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L195-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/IdxChange.lean#L195-L227

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}

theorem Formalism.DivisionValues.idxChange_lidx_add (p : Ideal R) [p.IsPrime] {e f g : Fin d → Fin d → K}
    (he : LinearIndependent K e) (hf : LinearIndependent K f) (hg : LinearIndependent K g) :
    lidx p (Submodule.span R (Set.range e)) (Submodule.span R (Set.range g)) =
      lidx p (Submodule.span R (Set.range e)) (Submodule.span R (Set.range f)) +
        lidx p (Submodule.span R (Set.range f)) (Submodule.span R (Set.range g)) := by sorry
