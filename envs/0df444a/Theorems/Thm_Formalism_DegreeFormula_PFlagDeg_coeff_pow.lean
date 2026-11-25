-- Prove2me | Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_coeff_pow
-- name    : Formalism.DegreeFormula.PFlagDeg.coeff_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:20.066074+00:00
-- url     : https://prove2.me/theorems/f949c7ea-2c65-47ec-af2e-d6044aa383f9
-- title:
--   PFlag Deg: coeff pow
-- statement:
--   The PFlag Deg construction uses the coeff pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L48-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DegreeFormula/PointDegree/FlagDeg.lean#L48-L103

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg
set_option maxRecDepth 4000

theorem Formalism.DegreeFormula.PFlagDeg.coeff_pow {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (lam : ι → Fin N → ℝ)
    (σ : ι → Equiv.Perm (Fin N)) :
    (linRoot lam ^ dimFl ι N).coeff (permExp σ) =
      (-1) ^ dimFl ι N * (((dimFl ι N).factorial : ℝ) / ((sfac N : ℝ) ^ Fintype.card ι)) *
        ∏ τ, ∏ i : Fin N, lam τ i ^ (N - 1 - ((σ τ i : Fin N) : ℕ)) := by sorry
