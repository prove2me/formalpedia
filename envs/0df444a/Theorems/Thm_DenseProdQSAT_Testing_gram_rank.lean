-- Prove2me | Theorems.Thm_DenseProdQSAT_Testing_gram_rank
-- name    : DenseProdQSAT.Testing.gram_rank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:57.867505+00:00
-- url     : https://prove2.me/theorems/fa5980c9-c449-4164-b725-27b36782f2c2
-- title:
--   Fact 4.8 — rank detected by principal Gram minors
-- statement:
--   Let $M$ be any complex matrix with $p$ rows and $q$ columns, and put $G=M^*M$. Sum the determinants of its $r$-element principal submatrices to obtain $E_r(M)$. Then
--
--   $$E_0(M)=1,\quad E_{q+1}(M)=0,\qquad E_r(M)\in\mathbb R,\quad E_r(M)>0\iff\operatorname{rank}M\ge r\quad(1\le r\le q).$$
--
--   The positivity comparison uses the real part of the sum and explicitly asserts its imaginary part is zero. This criterion converts dimension information into polynomial sign tests, and includes matrices with empty row or column sets.
--
--   Differences from the source:
--   - encoding: real-valued principal Gram-minor sums → complex sums with zero imaginary part and positivity of the real part; reason: the reality assertion makes the comparison exactly the source comparison
-- source:
--   Xuhong Liu, Shuai Shao, Zicheng Han, Xiande Zhang, STOC 2027 submission #35 (October 2026), Fact 4.8, Eq. (7), p. 13

import Definitions.Def_DenseProdQSAT_Testing_Algebra
set_option autoImplicit false

namespace DenseProdQSAT.Testing

theorem gram_rank {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) :
    GramSum M 0 = 1 ∧ GramSum M (q + 1) = 0 ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ q →
        (GramSum M r).im = 0 ∧ (0 < (GramSum M r).re ↔ r ≤ M.rank) := by sorry

end DenseProdQSAT.Testing
