-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_rem_eq
-- name    : Formalism.DegreeFormula.PPowSum.rem_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:33.801995+00:00
-- url     : https://prove2.me/theorems/36ab9921-90b0-4d4a-ab28-b1054171ccb7
-- title:
--   PPow Sum: rem eq
-- statement:
--   The PPow Sum construction uses the rem eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L89-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L89-L104

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula

theorem Formalism.DegreeFormula.PPowSum.rem_eq {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) (τ : ι)
    (k : ℕ) (j j' : Fin N) (hj : (j' : ℕ) = j + k) (hne : j ≠ j') :
    permExp (Pi.mulSingle τ (Equiv.swap j j') * σ) - Finsupp.single (τ, (σ τ).symm j') k =
      permExp σ - Finsupp.single (τ, (σ τ).symm j) k := by sorry
