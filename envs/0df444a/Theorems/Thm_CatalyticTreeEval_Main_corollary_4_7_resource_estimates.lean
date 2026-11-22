-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_corollary_4_7_resource_estimates
-- name    : CatalyticTreeEval.Main.corollary_4_7_resource_estimates
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:24:20.004561+00:00
-- url     : https://prove2.me/theorems/c7de1d4b-3fc8-4555-8106-c8d7a4822dc5
-- title:
--   Corollary 4.7 — subpolynomial catalyst and exponential-time resource estimates
-- statement:
--   Let $\epsilon>0$, put $t=\max(2,\lceil3/\epsilon\rceil)$, and fix the first $t$ odd primes. For a frame sequence with fixed modulus, fixed decoder sparsity $k\le3^t$, access scale $s=O(\ell)$, and dimension
--   $$
--   \log_2 d\le C_d\ell^{1/t}(\log_2(\ell+2))^{1-1/t},
--   $$
--   the exact resource expressions produced by Corollary 4.2 and a bare-input simulation admit uniform constants $C_s,C_c,C_t>0$ and a positive integer $q$ such that, for all $\ell,h\ge1$,
--   $$
--   \begin{aligned}
--   C_w(C_{s,0}(\ell+h(\operatorname{lg}k+\log_2m)+s)+s+1)&\le C_s(\ell+h),\\
--   C_{c,0}d(1+\log_2(dm))&\le 2^{C_c\ell^\epsilon},\\
--   C_{t,w}\Bigl(C_{t,0}(Bk)^h(2^\ell+k+d+2^s)^{q_0}+1\Bigr)(2^s+1)^{q_w}
--   &\le C_t2^{q(\ell+h)}.
--   \end{aligned}
--   $$
--   These are the analytic steps in the instantiation. Since $3/\epsilon\le t$, one has $1/t+\log_2(\ell+2)/\ell\le\epsilon$ for $\ell\ge1$, which converts the dimension estimate into the single subpolynomial exponent. The term $d$ occurs only through a fixed power in the time estimate, so that term is also absorbed by $2^{O(\ell)}$ rather than by polynomial time in $\ell$.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533, proof of Corollary 4.7, printed pp. 26–27 (PDF pp. 28–29), using the dimension bound from Corollary 3.11 Item 1, printed p. 17 (PDF p. 19), and the catalytic bound $O(d\log(dm))$ from Corollary 4.2, printed p. 21 (PDF p. 23).

import Definitions.Def_CatalyticTreeEval_Main_Framework

set_option autoImplicit false

/-- The real-arithmetic estimates in the instantiation of Corollary 4.7. -/
theorem CatalyticTreeEval.Main.corollary_4_7_resource_estimates
    (ε : ℝ) (hε : 0 < ε) {t : ℕ} (p : Fin t → ℕ) (hp : OddPrimeData p)
    (ht : t = max 2 ⌈3 / ε⌉₊)
    (F : List Bool → Frame) (k : ℕ) (Cd Csl : ℝ)
    (hCd : 0 < Cd) (hCsl : 0 < Csl)
    (hk : k ≤ 3 ^ t)
    (hF : ∀ l : ℕ, 1 ≤ l →
      (F (natCode l)).m = modulus p ∧
      (F (natCode l)).l = l ∧
      (F (natCode l)).k = k ∧
      ((F (natCode l)).d : ℝ) ≤ exp₂ (Cd * (l : ℝ) ^ (1 / (t : ℝ)) *
        (log₂ (l + 2)) ^ (1 - 1 / (t : ℝ))) ∧
      ((F (natCode l)).s : ℝ) ≤ Csl * l)
    (Cs0 Cc0 Ct0 B Cw Ctw : ℝ) (q0 qw : ℕ)
    (hCs0 : 0 < Cs0) (hCc0 : 0 < Cc0) (hCt0 : 0 < Ct0) (hB : 0 < B)
    (hCw : 0 < Cw) (hCtw : 0 < Ctw) (hq0 : 0 < q0) (hqw : 0 < qw) :
    ∃ (Cs Cc Ct : ℝ) (q : ℕ),
      0 < Cs ∧ 0 < Cc ∧ 0 < Ct ∧ 0 < q ∧
      ∀ h l : ℕ, 0 < h → 0 < l →
      let a := natCode l
      Cw * (Cs0 * ((F a).l + h * (lg (F a).k + log₂ (F a).m) + (F a).s) +
          (F a).s + 1) ≤ Cs * (l + h : ℝ) ∧
      Cc0 * (F a).d * (1 + log₂ ((F a).d * (F a).m)) ≤
        exp₂ (Cc * (l : ℝ) ^ ε) ∧
      Ctw * (Ct0 * (B * (F a).k) ^ h *
          ((2 : ℝ) ^ (F a).l + (F a).k + (F a).d + (2 : ℝ) ^ (F a).s) ^ q0 + 1) *
          ((2 : ℝ) ^ (F a).s + 1) ^ qw ≤
        Ct * (2 : ℝ) ^ (q * (l + h)) := by sorry
