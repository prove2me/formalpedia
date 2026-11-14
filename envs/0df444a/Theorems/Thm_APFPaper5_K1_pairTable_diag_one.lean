-- Prove2me | Theorems.Thm_APFPaper5_K1_pairTable_diag_one
-- name    : APFPaper5.K1.pairTable_diag_one
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:58:59.618619+00:00
-- url     : https://prove2.me/theorems/c0dee9f3-394b-4edf-a6dc-1d590375a3f2
-- title:
--   Nonzero repeatable marks have unit diagonal pair numbers
-- statement:
--   Let pᵢ lie in a ring with real algebra structure. Assume hp0: each pᵢ is nonzero; hidem: each is repeatable, pᵢ²=pᵢ; and h: the both-order pair relations pᵢpⱼpᵢ=cᵢⱼpᵢ hold. Then cᵢᵢ=1 for every i. This declaration establishes only the diagonal normalization from the stated algebraic data. It does not supply nonzero repeatable physical marks, identify these numbers with costs or frequencies, or place off-diagonal entries in the unit interval.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_pair_table_symm.lean:36; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_symmetry_retired_2026-11-12.md, ruling and not settled; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 312-350;476-512

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
theorem APFPaper5.K1.pairTable_diag_one (p : ι → A) (c : ι → ι → ℝ) (hp0 : ∀ i, p i ≠ 0)
    (hidem : ∀ i, p i * p i = p i) (h : PairNumbers p c) : ∀ i, c i i = 1 := by sorry
