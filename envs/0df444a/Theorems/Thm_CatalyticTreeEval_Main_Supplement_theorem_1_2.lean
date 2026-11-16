-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_theorem_1_2
-- name    : CatalyticTreeEval.Main.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:35:07.125445+00:00
-- url     : https://prove2.me/theorems/79f27c1d-721e-4886-addb-b9377ea28b40
-- title:
--   Theorem 1.2 (companion theorem; not used in the proof of the goal) — small-catalyst input-length tradeoff
-- statement:
--   For every positive binary-tree height and label length and every unrestricted full truth-table instance of serialized length $n$, there is one deterministic machine whose simultaneous resources, with positive-log conventions $L,L_2,L_3$, satisfy
--   $$S\le C_s L(n)\sqrt{L_2(n)}L_3(n),\quad C\le2^{2^{C_c\sqrt{L_2(n)}}},\quad T\le(n+1)^{C_t\sqrt{L_2(n)}}.$$
--   It outputs the entire root label and restores every arbitrary catalytic bit. This is the companion small-catalyst tradeoff; Corollary 4.8 supplies its parameterized support, and small valid inputs are included. The catalyst is bounded by a prefix of each longer arbitrary tape, with whole-tape restoration.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: log n, log log n and log log log n in asymptotic bounds → L(n)=1+log₂(n+1), L₂(n)=1+log₂ L(n), L₃(n)=1+log₂ L₂(n), with n the full serialized input length; reason: positive-log conventions preserve the stated asymptotics and include every small valid input
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Theorem 1.2, printed p. 1 (PDF p. 3)

import Definitions.Def_CatalyticTreeEval_Main_Supplement_UniformConstructions

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem theorem_1_2 :
    ∃ (M : Machine) (Cs Cc Ct : ℝ), 0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧
      ∀ h l : ℕ, 0 < h → 0 < l → ∀ I : Tree l h,
      let n := I.encode.length
      ComputesPrefix M I.encode (bits l I.value.val)
        (Cs * lg n * Real.sqrt (loglog n) * logloglog n)
        (exp₂ (exp₂ (Cc * Real.sqrt (loglog n))))
        (((n : ℝ) + 1) ^ (Ct * Real.sqrt (loglog n))) := by sorry

end CatalyticTreeEval.Main.Supplement
