-- Prove2me | Theorems.Thm_APFPaper5_K1_pairNumbers_symm
-- name    : APFPaper5.K1.pairNumbers_symm
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:58:46.350631+00:00
-- url     : https://prove2.me/theorems/fdd80795-09d8-43c9-b3f1-0b57feda1c4c
-- title:
--   Pair relations in both orders force symmetric numbers for nonzero marks
-- statement:
--   Let pᵢ be elements of a ring with a real algebra structure, and let cᵢⱼ be real numbers. Assume hp0: every pᵢ is nonzero, and h: pᵢpⱼpᵢ=cᵢⱼpᵢ for every ordered pair. Then cᵢⱼ=cⱼᵢ. Both orders are included in the supplied NUMBERS predicate. No separate symmetry assumption or idempotence is required. The conclusion establishes neither existence of these relations at a physical interface nor positivity, a unit interval bound, or availability of reversed physical processes.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_pair_table_symm.lean:27; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_symmetry_retired_2026-11-12.md, ruling and not settled; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 312-350;476-512

import Definitions.Def_APFPaper5_K1_PairNumbers
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Theorems.Thm_APFPaper1_RecordBook_pair_number_symm
import Theorems.Thm_APFPaper1_RecordBook_pair_table_symm
import Theorems.Thm_APFPaper1_RecordBook_pair_number_self

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u uA
variable {ι : Type u} [Fintype ι] {A : Type uA} [Ring A] [Algebra ℝ A]

omit [Fintype ι] in
theorem APFPaper5.K1.pairNumbers_symm (p : ι → A) (c : ι → ι → ℝ) (hp0 : ∀ i, p i ≠ 0)
    (h : PairNumbers p c) : ∀ i j, c i j = c j i := by sorry
