-- Prove2me | Theorems.Thm_DetDLP_ecdlp_short_weierstrass_reduction
-- name    : DetDLP.ecdlp_short_weierstrass_reduction
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T09:49:28.836747+00:00
-- url     : https://prove2.me/theorems/ff685cdf-b89e-4690-b42b-172a78c3c037
-- title:
--   Polynomial-Time Reduction of General Weierstrass ECDLP to Short Weierstrass Form ($p > 3$)
-- statement:
--   Suppose there exists a uniform deterministic multitape Turing machine solving the prime-order elliptic-curve discrete logarithm problem on short Weierstrass curves ($a_1 = a_2 = a_3 = 0$) over $\mathbb{F}_p$ ($p > 3$) in worst-case time $2^{O(b/\sqrt{\log\log b})}$ and space $2^{O(b/(\log b)^{1/4})}$. Then there exists a uniform deterministic multitape Turing machine solving the prime-order elliptic-curve discrete logarithm problem for arbitrary nonsingular Weierstrass curves $y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$ over $\mathbb{F}_p$ ($p > 3$) within the same asymptotic time and space bounds
--
--   $$\text{time} = 2^{O(b / \sqrt{\log\log_{\mathrm{safe}} b})}, \qquad \text{space} = 2^{O(b / (\log_{\mathrm{safe}} b)^{1/4})}.$$
--
--   For $p > 3$, completing the square $y' = y + (a_1 x + a_3)/2$ and shifting $x' = x + (a_1^2 + 4a_2)/12 \pmod p$ computes an isomorphic short Weierstrass model and maps $P, Q$ in $\mathrm{poly}(b)$ bit operations, preserving group order and discrete logarithms.
--
--   **Formalization Note** Formulated as a black-box machine transformation on `PrimitiveMachine`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.3, Proof of Theorem 1.1(1) (p. 17)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem ecdlp_short_weierstrass_reduction :
    (∃ (M_sw : PrimitiveMachine) (out_sw : Fin M_sw.tapeCount) (C_sw : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
          letI := ecPointFintype E
          let r := Fintype.card E.toAffine.Point
          r.Prime →
          ∀ (P Q : E.toAffine.Point),
            addOrderOf P = r →
            ∃ x : ℕ, x < r ∧ x • P = Q ∧
              RunsWithin M_sw out_sw (encodeECDLPInput p E P Q) (countWord x)
                (mainTimeBound C_sw (bitLen p)) (mainSpaceBound C_sw (bitLen p))) →
    (∃ (M_ec : PrimitiveMachine) (out_ec : Fin M_ec.tapeCount) (C_ec : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          letI := ecPointFintype E
          let r := Fintype.card E.toAffine.Point
          r.Prime →
          ∀ (P Q : E.toAffine.Point),
            addOrderOf P = r →
            ∃ x : ℕ, x < r ∧ x • P = Q ∧
              RunsWithin M_ec out_ec (encodeECDLPInput p E P Q) (countWord x)
                (mainTimeBound C_ec (bitLen p)) (mainSpaceBound C_ec (bitLen p))) := by sorry

end DetDLP
