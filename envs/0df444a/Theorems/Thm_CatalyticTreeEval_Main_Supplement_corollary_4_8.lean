-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_corollary_4_8
-- name    : CatalyticTreeEval.Main.Supplement.corollary_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:34:34.452291+00:00
-- url     : https://prove2.me/theorems/4cc458c9-7e6b-41e8-9882-bb7dbfb355f0
-- title:
--   Corollary 4.8 (used in the proof of Theorem 1.2) — parameterized small-catalyst tradeoff
-- statement:
--   For all heights $h\ge1$ and all label lengths $\ell$ above one absolute threshold, one deterministic machine evaluates every binary tree with arbitrary full truth tables. It outputs all $\ell$ root bits and restores every bit of every initially arbitrary catalytic tape. With uniform positive constants, its simultaneous resources are
--   $$S\le C_s(\ell+h\sqrt{\log_2\ell}\log_2\log_2\ell),\quad C\le2^{2^{C_c\sqrt{\log_2\ell}}},\quad T\le2^{C_t(\ell+h\sqrt{\log_2\ell})}.$$
--   This parameterized tradeoff supports Theorem 1.2. The catalyst predicate holds for every tape at least as long as the ceiling of the displayed bound, restores the whole tape, and never reaches the right end of the permitted prefix.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: ℓ larger than a sufficiently large absolute constant → one existential integer threshold L≥4 and L≤ℓ; reason: avoids undefined iterated logarithms; taking an integer ceiling and increasing an unspecified threshold preserves the source domain
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Corollary 4.8, printed p. 27 (PDF p. 29)

import Definitions.Def_CatalyticTreeEval_Main_Resources

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem corollary_4_8 :
    ∃ (M : Machine) (Cs Cc Ct : ℝ) (L : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 4 ≤ L ∧
      ∀ h l : ℕ, 0 < h → L ≤ l → ∀ I : Tree l h,
      ComputesPrefix M I.encode (bits l I.value.val)
        (Cs * (l + h * Real.sqrt (log₂ l) * log₂ (log₂ l)))
        (exp₂ (exp₂ (Cc * Real.sqrt (log₂ l))))
        (exp₂ (Ct * (l + h * Real.sqrt (log₂ l)))) := by sorry

end CatalyticTreeEval.Main.Supplement
