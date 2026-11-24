-- Prove2me | Theorems.Thm_BB6Kit_prop37_expand
-- name    : BB6Kit.prop37_expand
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-24T06:34:38.053617+00:00
-- url     : https://prove2.me/theorems/96771e89-9023-47ee-b7ac-83a549151e16
-- title:
--   Expansion (3.10): $\Delta=\alpha^{M}\sum_{\mathcal I}(\Lambda')^{N-|\mathcal I|}\Psi_{\mathcal I}(1)$
-- statement:
--   The algebraic expansion step (3.10) in the proof of Proposition 3.7 of the Mignotte–Voutier kit.
--
--   **Theorem.** Let $K\ge3$, $L\ge5$, $N=K(K+1)L/2\le RST$, integers $\alpha_j>1$ and $b_j>0$, with $\Lambda=b_1\log\alpha_1+b_2\log\alpha_2-b_3\log\alpha_3\ne0$. Let the rows enumerate the triples $(k,m,\ell)$ with $k+m\le K-1$, $\ell<L$, and let the columns be $N$ distinct triples in the box. Then the interpolation determinant (2.6) satisfies $$\Delta=\alpha_1^{M_1}\alpha_2^{M_2}\alpha_3^{M_3}\sum_{\mathcal I\subseteq\{1,\dots,N\}}(\Lambda')^{N-|\mathcal I|}\,\Psi_{\mathcal I}(1),$$ with $\Psi_{\mathcal I}$ as in `BB6Psi.psi`.
--
--   The proof has three steps:
--
--   1. Factor $\alpha_j^{(L-1)c_j/2}$ out of each column, and use $\sum_i\lambda_i=0$.
--   2. Use row operations, which are triangular in $(k,m)$, to replace $\binom{b'_3(r+t\beta_1)}{k}\binom{b''_3(s+t\beta_2)}{m}$ by its leading term $\tfrac{b_3'^k b_3''^m}{k!m!}\eta^k\zeta^m$.
--   3. Expand each factor $1+\theta_{i,j}\Lambda'$ multilinearly over the rows.
--
--   This is a pure identity: it involves no estimates. Checked numerically on several instances.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Section 3.3, eqs. (3.5)-(3.10) (proof of Proposition 3.7).

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi

namespace BB6Kit
theorem prop37_expand (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst) :
    ((BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst : ℝ) : ℂ) =
      (((α1 : ℝ) ^ (BB6Kit.MK L N rst Prod.fst) * (α2 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.1)) *
          (α3 : ℝ) ^ (BB6Kit.MK L N rst (fun x => x.2.2)) : ℝ) : ℂ) *
        ∑ I ∈ (Finset.univ : Finset (Fin N)).powerset,
          ((BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ^ (N - I.card) : ℝ) : ℂ) * BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I 1 := by
  sorry
end BB6Kit
