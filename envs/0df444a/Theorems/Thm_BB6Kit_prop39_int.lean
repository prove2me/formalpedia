-- Prove2me | Theorems.Thm_BB6Kit_prop39_int
-- name    : BB6Kit.prop39_int
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T22:12:56.325795+00:00
-- url     : https://prove2.me/theorems/be490290-6cc5-4ff4-8fac-7441078a516c
-- title:
--   Mignotte–Voutier Prop. 3.9 for integer $\alpha$: $\log|\Delta|\ge\sum_j (M_j-G_j)\log\alpha_j$
-- statement:
--   The arithmetic (Liouville) lower bound for the interpolation determinant: Proposition 3.9 of the Mignotte–Voutier kit for rational-integer $\alpha_j\ge 1$, where $D=1$ and $h(\alpha)=\log\alpha$.
--
--   **Theorem.** With rows and columns as in `BB6Kit.prop37`, $K\ge 3$, $L\ge 5$, $N\le RST$, if $\Delta\ne 0$ then $$\log|\Delta|\ge\sum_{j=1}^3 (M_j-G_j)\log\alpha_j.$$
--
--   Proof idea: every monomial of $\Delta$ has exponent of $\alpha_j$ at least $M_j-G_j$ (Lemma 3.2, i.e. Lemme 4 of Laurent–Mignotte–Nesterenko). So $\Delta/\prod_j\alpha_j^{\lceil M_j-G_j\rceil}$ is a nonzero integer. This strengthens `BB6Baker.liouville_delta` ($|\Delta|\ge 1$), which is the case of trivial exponents.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Proposition 3.9 and Lemma 3.2 (Lemme 4 of Laurent–Mignotte–Nesterenko, J. Number Theory 55 (1995)), specialised to D=1, integer alpha.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem prop39_int (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 ≤ α1) (hα2 : 1 ≤ α2) (hα3 : 1 ≤ α3)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst)
    (hne : BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst ≠ 0) :
    BB6Kit.MK L N rst Prod.fst * Real.log (α1 : ℝ) + BB6Kit.MK L N rst (fun x => x.2.1) * Real.log (α2 : ℝ) + BB6Kit.MK L N rst (fun x => x.2.2) * Real.log (α3 : ℝ) - (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) + BB6Kit.GK N L R S T T * Real.log (α3 : ℝ)) ≤ Real.log |BB6Delta.deltaR N (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) α1 α2 α3 kml rst| := by
  sorry
end BB6Kit
