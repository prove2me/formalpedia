-- Prove2me | Theorems.Thm_BarvinokCount_ShortFormula_two_pow_iterCount_le
-- name    : BarvinokCount.ShortFormula.two_pow_iterCount_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:51:43.836579+00:00
-- url     : https://prove2.me/theorems/d841c7f8-88bf-4ddb-9359-4d5b6bfd3d12
-- title:
--   Proof of Theorem 5.4, display p. 777 — (2^d)^T ≤ C_1(d)·(log Ind K)^{C_2(d)}
-- statement:
--   Let $d\ge2$ and let $N\ge2$ be an integer (in the paper $N=\operatorname{Ind}K$), and let $T=T(d,N)$ be the smallest integer with $T\ge(-\log\log1.9+\log\log N)/(\log d-\log(d-1))$. Put
--   $$C_1(d)=\exp\Bigl\{\Bigl(\frac{-\log\log1.9}{\log d-\log(d-1)}+1\Bigr)\cdot\log(2^d)\Bigr\},\qquad C_2(d)=\frac{\log(2^d)}{\log d-\log(d-1)} .$$
--   Then
--   $$(2^d)^T\le C_1(d)\cdot(\log N)^{C_2(d)} .$$
--
--   For fixed $d$, $C_1$ and $C_2$ are constants and $\log\operatorname{Ind}K$ is bounded by a polynomial in the input size, so this inequality is what makes the number of primitive cones in Theorem 5.4 polynomial.
--
--   **Formalization Note** The hypothesis $N\ge2$ is added: for $N=1$, $\log N=0$ and the right side is $0$ while the left side is $1$ (and $\log\log1$ in the definition of $T$ is undefined). The exponent $C_2(d)$ is a real power of the positive number $\log N$. Natural logarithms.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), p. 777, proof of Theorem 5.4 (definitions of C_1(d), C_2(d) and the display (2^d)^T ≤ C_1(d)·(log(Ind K))^{C_2(d)})

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_iterCount

namespace BarvinokCount.ShortFormula

theorem two_pow_iterCount_le {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    (((2 : ℝ) ^ d) ^ iterCount d N) ≤
      Real.exp (((-Real.log (Real.log (1.9 : ℝ))) / (Real.log (d : ℝ) - Real.log ((d : ℝ) - 1)) + 1) *
          Real.log ((2 : ℝ) ^ d)) *
        (Real.log (N : ℝ)) ^
          (Real.log ((2 : ℝ) ^ d) / (Real.log (d : ℝ) - Real.log ((d : ℝ) - 1))) := by sorry

end BarvinokCount.ShortFormula
