-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_theorem_3_4
-- name    : CatalyticTreeEval.Main.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:39:52.88106+00:00
-- url     : https://prove2.me/theorems/2774603a-30ff-498a-a25d-64e77d11f5cf
-- title:
--   Theorem 3.4 (companion theorem; not used in the proof of the goal) — Cook–Mertz ordinary-space bound
-- statement:
--   For all positive heights $h$ and label lengths $\ell$, one ordinary deterministic binary machine evaluates every unrestricted binary tree given by its explicit truth tables and leaf labels. If the serialized input length is $n$, it outputs the entire root label using
--   $$S\le C_s L(n)L_2(n).$$
--   It has no catalytic storage and no assumed efficient evaluator. This recalled Cook–Mertz result is proved within the paper through Corollary 4.9.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: log n, log log n and log log log n in asymptotic bounds → L(n)=1+log₂(n+1), L₂(n)=1+log₂ L(n), L₃(n)=1+log₂ L₂(n), with n the full serialized input length; reason: positive-log conventions preserve the stated asymptotics and include every small valid input
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Theorem 3.4, printed p. 15 (PDF p. 17)

import Definitions.Def_CatalyticTreeEval_Main_Supplement_UniformConstructions

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem theorem_3_4 :
    ∃ (M : Machine) (Cs : ℝ), 0 < Cs ∧
      ∀ h l : ℕ, 0 < h → 0 < l → ∀ I : Tree l h,
      Prints M I.encode (bits l I.value.val)
        (Cs * lg I.encode.length * loglog I.encode.length) := by sorry

end CatalyticTreeEval.Main.Supplement
