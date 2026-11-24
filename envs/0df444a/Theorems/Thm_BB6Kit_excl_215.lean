-- Prove2me | Theorems.Thm_BB6Kit_excl_215
-- name    : BB6Kit.excl_215
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T22:13:09.144034+00:00
-- url     : https://prove2.me/theorems/c3f779ce-716b-456d-8a15-ce2e5cba52dd
-- title:
--   Degeneracy (2.15) cannot occur for $b=(k-1,1,i)$ with the explicit parameters
-- statement:
--   **Lemma (no degeneracy (2.15)).** Let $n\ge 60$, $2^n\le i<2^{n+1}$, $1\le c\le 4i$, $2\le k\le 2i+2$, and suppose $|\Lambda|<1$ for $\Lambda=(k-1)\log 2-i\log 3+\log c$. With the parameter family of `BB6Kit`, there are no integers $u_1,u_2,u_3$ with $u_1(k-1)+u_2+u_3 i=0$, $\gcd(u_1,u_2,u_3)=1$, and the size bounds of condition (2.15) of the Mignotte–Voutier kit.
--
--   Proof idea: the bounds give $|u_1|,|u_3|\le 8$ and $|u_2|\ll n^2$. Eliminating $k$ gives $i(u_1\log3+u_3\log2)=u_1(\log c-\Lambda)-u_2\log 2$. If $(u_1,u_3)\ne(0,0)$, the left side is at least $0.05\,i$ because $|q\log3-p\log2|>0.05$ for $1\le q,p\le 8$. The right side is polylogarithmic in $i$. Otherwise $u_2=0$, contradicting the gcd condition.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Theorem 2.1 condition (2.15); argument new.

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit

namespace BB6Kit
theorem excl_215 (n i k c : ℕ) (hn : 60 ≤ n) (hi : 2 ^ n ≤ i) (hi' : i < 2 ^ (n + 1))
    (hc : 0 < c) (hc4 : c ≤ 4 * i) (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2)
    (hsmall : |((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ)| < 1) :
    ¬ (∃ u1 u2 u3 : ℤ, u1 * ((k - 1 : ℕ) : ℤ) + u2 * ((1 : ℕ) : ℤ) + u3 * ((i) : ℤ) = 0 ∧ Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 ∧
        (|u1| : ℝ) ≤ (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1) / ((max (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fS1 n) + 1) (((BB6Kit.fS1 n) : ℝ) + (BB6Kit.fR1 n) + 1)) (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fR1 n) + 1) ((BB6Kit.fChi n) * Real.sqrt ((((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1))))) - max ((BB6Kit.fS1 n) : ℝ) (BB6Kit.fR1 n)) ∧
        (|u2| : ℝ) ≤ (((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1) / ((max (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fS1 n) + 1) (((BB6Kit.fS1 n) : ℝ) + (BB6Kit.fR1 n) + 1)) (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fR1 n) + 1) ((BB6Kit.fChi n) * Real.sqrt ((((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1))))) - max ((BB6Kit.fR1 n) : ℝ) (BB6Kit.fR1 n)) ∧
        (|u3| : ℝ) ≤ (((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) / ((max (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fS1 n) + 1) (((BB6Kit.fS1 n) : ℝ) + (BB6Kit.fR1 n) + 1)) (max (((BB6Kit.fR1 n) : ℝ) + (BB6Kit.fR1 n) + 1) ((BB6Kit.fChi n) * Real.sqrt ((((BB6Kit.fR1 n) : ℝ) + 1) * (((BB6Kit.fS1 n) : ℝ) + 1) * (((BB6Kit.fR1 n) : ℝ) + 1))))) - max ((BB6Kit.fR1 n) : ℝ) (BB6Kit.fS1 n))) := by
  sorry
end BB6Kit
