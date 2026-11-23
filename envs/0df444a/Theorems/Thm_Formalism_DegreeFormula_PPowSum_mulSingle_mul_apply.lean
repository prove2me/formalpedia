-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_mulSingle_mul_apply
-- name    : Formalism.DegreeFormula.PPowSum.mulSingle_mul_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:21.16119+00:00
-- url     : https://prove2.me/theorems/f9d7bee2-7137-49ca-8aaf-429479193de6
-- title:
--   PPow Sum: mul Single mul apply
-- statement:
--   The PPow Sum construction uses the mul Single mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L80-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L80-L87

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

theorem Formalism.DegreeFormula.PPowSum.mulSingle_mul_apply {ι : Type} [DecidableEq ι] {N : ℕ} (τ : ι) (s : Equiv.Perm (Fin N))
    (σ : ι → Equiv.Perm (Fin N)) (t : ι) (i : Fin N) :
    ((Pi.mulSingle τ s * σ : ι → Equiv.Perm (Fin N)) t) i = if t = τ then s (σ τ i) else σ t i := by sorry
