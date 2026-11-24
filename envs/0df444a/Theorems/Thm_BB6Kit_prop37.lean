-- Prove2me | Theorems.Thm_BB6Kit_prop37
-- name    : BB6Kit.prop37
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T22:13:00.825724+00:00
-- url     : https://prove2.me/theorems/8c3abd11-f1dd-42d9-a47c-6ca33ff0e010
-- title:
--   Mignotte–Voutier Prop. 3.7: analytic upper bound for the interpolation determinant (integer $\alpha$, real case)
-- statement:
--   The analytic upper bound for the interpolation determinant: Proposition 3.7 of the Mignotte–Voutier kit, in the real case with rational-integer $\alpha_j>1$ ($D=1$).
--
--   Let $\Lambda=b_1\log\alpha_1+b_2\log\alpha_2-b_3\log\alpha_3\ne 0$ with $b_j>0$, $\gcd(b_1,b_2,b_3)=1$, $\alpha_1,\alpha_2,\alpha_3$ multiplicatively independent. Let $K\ge 3$, $L\ge 5$, $N=K(K+1)L/2\le RST$, $\rho\ge 2$, rows enumerating $\{(k,m,\ell): k+m\le K-1, \ell<L\}$ and $N$ distinct columns in $[0,R)\times[0,S)\times[0,T)$, and $\Delta$ the determinant (2.6) (`BB6Delta.deltaR`). **Theorem.** If $\Lambda'<\rho^{-KL}$ then $$\log|\Delta|<\sum_j M_j\log\alpha_j+\rho\sum_j G_j\log\alpha_j+\log N!+N\log 2+\tfrac{N(K-1)}{3}\log b-\tfrac{N^2}{2K}\Bigl(1-\tfrac{2}{3L}-\tfrac{2}{3KL}-\tfrac{1}{3L^2}-\tfrac{16}{3K^2L}\Bigr)\log\rho+0.001,$$ stated as $|\Delta|<\exp(\cdots)$. The proof uses Schwarz's lemma and the multiplicity estimate (Lemma 3.6).
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Proposition 3.7 (with notation of Section 2.2 and Lambda' of Theorem 2.1), real case, D=1.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem prop37 (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ) (ρ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0) (hρ : 2 ≤ ρ)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst)
    (hsmall : BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) < ρ ^ (-((K : ℝ) * L))) :
    |BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst| <
      Real.exp (BB6Kit.MK L N rst Prod.fst * Real.log (α1 : ℝ) + BB6Kit.MK L N rst (fun x => x.2.1) * Real.log (α2 : ℝ) + BB6Kit.MK L N rst (fun x => x.2.2) * Real.log (α3 : ℝ) + ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) + BB6Kit.GK N L R S T T * Real.log (α3 : ℝ)) + Real.log (N.factorial : ℝ) + (N : ℝ) * Real.log 2 +
        (N : ℝ) * ((K : ℝ) - 1) / 3 * Real.log (BB6Kit.bK K R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3)) -
        (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 - 2 / (3 * (L : ℝ)) - 2 / (3 * (K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2) -
          16 / (3 * (K : ℝ) ^ 2 * L)) * Real.log ρ + 0.001) := by
  sorry
end BB6Kit
