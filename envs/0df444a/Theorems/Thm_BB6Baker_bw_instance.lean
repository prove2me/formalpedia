-- Prove2me | Theorems.Thm_BB6Baker_bw_instance
-- name    : BB6Baker.bw_instance
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T17:55:56.828191+00:00
-- url     : https://prove2.me/theorems/7e3d53dd-b452-4ec9-8466-a79e7f368220
-- title:
--   Linear form in $\log 2, \log 3, \log c$: explicit Baker–Wüstholz lower bound
-- statement:
--   Let $\Lambda = (k-1)\log 2 - i\log 3 + \log c$ with $i \ge 2^{60}$, $1 \le c \le 4i$, $2 \le k \le 2i+2$. **Theorem.** If $\Lambda \ne 0$ then $\log|\Lambda| \ge -2^{42}\,\log(2i+2)\,\log 3\,\log(4i)$.
--
--   This is the special case $K=\mathbb Q$, $n=3$, $\alpha=(2,3,c)$ of the Baker–Wüstholz theorem: the constant $C(3,1) \le 2^{42}$, the modified heights are $1$, $\log 3$ and $\le \log(4i)$, and $B \le 2i+2$. It is the only transcendence input needed for the non-halting of the BB(6) machine `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` (currently an axiom in rwst/bbchallenge). An axiom-free proof could follow Laurent's interpolation-determinant method for three logarithms.
-- source:
--   Implied by Matveev, Izv. Math. 64 (2000) 1217-1269 (restated as Bugeaud-Mignotte-Siksek, Ann. Math. 163 (2006), Thm 9.4). Verified against two independent open-access restatements that agree verbatim: arXiv:1905.01015 Thm 2.3 and arXiv:2207.12860 (Ddamulira-Luca) Thm 2.2: for positive real γ_i in a real field of degree D, Γ = ∏γ_i^{b_i} - 1 ≠ 0 ⇒ log|Γ| > -1.4·30^{t+3}·t^{4.5}·D²(1+log D)(1+log B)A_1⋯A_t, A_i ≥ max(D h(γ_i), |log γ_i|, 0.16). Here t=3, D=1, γ=(2,3,c), b=(k-1,-i,1), B ≤ 2i+1, A=(log 2, log 3, max(log c,0.16) ≤ log 4i): constant ≈ 9.9e10 vs 2^42 ≈ 4.4e12, margin ≈ 43x (checked for i=2^60..2^200); passing from Γ to Λ = log(Γ+1) costs at most log 2. Also implied by Baker-Wüstholz, J. reine angew. Math. 442 (1993) 19-62 (constant 2^42 as in rwst/bbchallenge, CC0).

import Mathlib

namespace BB6Baker
theorem bw_instance (i k c : ℕ) (hi : 2 ^ 60 ≤ i) (hc : 0 < c) (hc4 : c ≤ 4 * i)
    (hk2 : 2 ≤ k) (hk : k ≤ 2 * i + 2)
    (hne : ((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ) ≠ 0) :
    -(2 ^ 42 * Real.log (2 * (i : ℝ) + 2) * Real.log 3 * Real.log (4 * (i : ℝ))) ≤
      Real.log |((k : ℝ) - 1) * Real.log 2 - (i : ℝ) * Real.log 3 + Real.log (c : ℝ)| := by
  sorry
end BB6Baker
