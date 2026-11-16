-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_corollary_4_9
-- name    : CatalyticTreeEval.Main.Supplement.corollary_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:38:40.921192+00:00
-- url     : https://prove2.me/theorems/eb5ea18e-6fef-4798-93cf-ecbb4f8d16d5
-- title:
--   Corollary 4.9 (used in the proof of Theorem 3.4) — parameterized and input-length ordinary bounds
-- statement:
--   One ordinary deterministic binary machine outputs the whole root label of every unrestricted binary TreeEval instance, for all positive $h,\ell$. With fixed positive constants, its parameterized bounds are
--   $$S\le C_s(\ell+h\log_2(\ell+2)),\qquad T\le2^{C_t(\ell+h\log_2(\ell+2))}.$$
--   For the same machine, writing $n$ for the serialized input length, the input-length bounds also hold:
--   $$S\le C_s L(n)L_2(n),\qquad T\le(n+1)^{C_tL_2(n)}.$$
--   There is no catalytic tape. Both clauses are retained; the ordinary-space clause supplies the proof of recalled Theorem 3.4.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: log n, log log n and log log log n in asymptotic bounds → L(n)=1+log₂(n+1), L₂(n)=1+log₂ L(n), L₃(n)=1+log₂ L₂(n), with n the full serialized input length; reason: positive-log conventions preserve the stated asymptotics and include every small valid input
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Corollary 4.9, printed p. 27 (PDF p. 29)

import Definitions.Def_CatalyticTreeEval_Main_Supplement_UniformConstructions

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem corollary_4_9 :
    ∃ (M : Machine) (Cs Ct : ℝ), 0 < Cs ∧ 0 < Ct ∧
      ∀ h l : ℕ, 0 < h → 0 < l → ∀ I : Tree l h,
      PrintsIn M I.encode (bits l I.value.val)
        (Cs * (l + h * log₂ (l + 2)))
        (exp₂ (Ct * (l + h * log₂ (l + 2)))) ∧
      PrintsIn M I.encode (bits l I.value.val)
        (Cs * lg I.encode.length * loglog I.encode.length)
        (((I.encode.length : ℝ) + 1) ^ (Ct * loglog I.encode.length)) := by sorry

end CatalyticTreeEval.Main.Supplement
