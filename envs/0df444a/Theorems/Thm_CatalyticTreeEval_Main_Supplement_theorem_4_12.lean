-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_Supplement_theorem_4_12
-- name    : CatalyticTreeEval.Main.Supplement.theorem_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:41:59.246212+00:00
-- url     : https://prove2.me/theorems/46a7b0c0-c027-4145-a402-d83ba8d7a8b2
-- title:
--   Theorem 4.12 (companion theorem; not used in the proof of the goal) — space bound for every block size
-- statement:
--   For all positive heights $h$ and label lengths $\ell$, and every integer $1\le b\le h$, an ordinary deterministic binary machine evaluates every unrestricted binary TreeEval instance and outputs its whole root label using
--   $$S\le C_s\left(h+2^b\ell+\frac{h}{b}\log_2(\ell+2)\right).$$
--   The machine and positive constant are uniform over $h,\ell,b$; the requested block size $b$ is supplied in a binary header. No catalytic storage, divisibility condition on $h$, or upper bound on $2^b$ is imposed. This is the full Stoeckl–Goldreich blocking companion theorem, including incomplete final blocks.
--
--   Differences from the source:
--   - encoding: asymptotic algorithmic resource bounds → a finite binary machine and positive uniform constants, with fixed polynomial degrees where needed; reason: expands O/poly using actual transitions and visited work cells; constants precede varying inputs and tapes
--   - encoding: integer block size b and fraction h/b → a binary b header and real division (h:ℝ)/(b:ℝ); reason: b≥1 prevents zero division; no divisibility restriction or truncated quotient is introduced
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), canonical source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238, Theorem 4.12, printed p. 29 (PDF p. 31)

import Definitions.Def_CatalyticTreeEval_Main_Resources

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

theorem theorem_4_12 :
    ∃ (M : Machine) (Cs : ℝ), 0 < Cs ∧
      ∀ h l b : ℕ, 0 < h → 0 < l → 1 ≤ b → b ≤ h → ∀ I : Tree l h,
      Prints M (natCode b ++ I.encode) (bits l I.value.val)
        (Cs * (h + (2 : ℝ) ^ b * l + (h : ℝ) / (b : ℝ) * log₂ (l + 2))) := by sorry

end CatalyticTreeEval.Main.Supplement
