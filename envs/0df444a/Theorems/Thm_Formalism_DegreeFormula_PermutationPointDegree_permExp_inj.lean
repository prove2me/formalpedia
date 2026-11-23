-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PermutationPointDegree_permExp_inj
-- name    : Formalism.DegreeFormula.PermutationPointDegree.permExp_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:34.984062+00:00
-- url     : https://prove2.me/theorems/91f59fc2-947c-41ea-864f-e546463e6c80
-- title:
--   Permutation Point Degree: perm Exp inj
-- statement:
--   The Permutation Point Degree construction uses the perm Exp inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PermExpInj.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PermExpInj.lean#L8-L16

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PermutationPointDegree
open Formalism.DegreeFormula

theorem Formalism.DegreeFormula.PermutationPointDegree.permExp_inj {ι : Type} [Fintype ι] {N : ℕ} (σ ρ : ι → Equiv.Perm (Fin N))
    (h : permExp σ = permExp ρ) : σ = ρ := by sorry
