-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_permSign_mulSingle_swap_mul
-- name    : Formalism.DegreeFormula.PPowSum.permSign_mulSingle_swap_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:31.749467+00:00
-- url     : https://prove2.me/theorems/50e2f2e5-3416-40bf-aa76-3d04f29468d2
-- title:
--   PPow Sum: perm Sign mul Single swap mul
-- statement:
--   The PPow Sum construction uses the perm Sign mul Single swap mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L66-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L66-L78

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

theorem Formalism.DegreeFormula.PPowSum.permSign_mulSingle_swap_mul {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (a b : Fin N)
    (hab : a ≠ b) (σ : ι → Equiv.Perm (Fin N)) :
    sgnP (Pi.mulSingle τ (Equiv.swap a b) * σ) = -sgnP σ := by sorry
