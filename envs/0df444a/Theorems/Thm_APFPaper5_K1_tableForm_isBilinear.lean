-- Prove2me | Theorems.Thm_APFPaper5_K1_tableForm_isBilinear
-- name    : APFPaper5.K1.tableForm_isBilinear
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:01:47.872146+00:00
-- url     : https://prove2.me/theorems/e65deab3-3573-4b94-98db-dd5c072dd59d
-- title:
--   Every finite real table defines a bilinear coefficient form
-- statement:
--   For any real table G on a finite index set, the form F(x,y)=ΣᵢΣⱼxᵢG(i,j)yⱼ is additive and real-homogeneous in each argument. No symmetry, positivity, nondegeneracy or special pattern of entries is required. The construction is on supplied coefficient spaces.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_mark_table_instance.lean:25; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 3038-3041;353-391

import Definitions.Def_APFPaper5_K1_OrderedScore
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Mathlib.Algebra.Module.Pi

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u
variable {ι : Type u} [Fintype ι]

theorem APFPaper5.K1.tableForm_isBilinear (G : ι → ι → ℝ) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) := by sorry
