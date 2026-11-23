-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PPowSum_slice
-- name    : Formalism.DegreeFormula.PPowSum.slice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:43.465139+00:00
-- url     : https://prove2.me/theorems/881999de-cbed-4ad4-95df-48a54dff03e7
-- title:
--   PPow Sum: slice
-- statement:
--   The PPow Sum construction uses the slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L112-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/PowSum.lean#L112-L139

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

theorem Formalism.DegreeFormula.PPowSum.slice {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (k : ℕ) (hk : 1 ≤ k)
    (P : MvPolynomial (ι × Fin N) ℝ) (j : Fin N) :
    ∑ σ : ι → Equiv.Perm (Fin N), sgnP σ * (X (τ, (σ τ).symm j) ^ k * P).coeff (permExp σ) = 0 := by sorry
