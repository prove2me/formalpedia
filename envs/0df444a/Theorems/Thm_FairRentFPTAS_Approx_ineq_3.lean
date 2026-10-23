-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_ineq_3
-- name    : FairRentFPTAS.Approx.ineq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:41.347984+00:00
-- url     : https://prove2.me/theorems/89a1351e-a49a-4c35-8b4f-81805f3aad76
-- title:
--   Inequality (3), proof of Theorem 1, p. 13 — a stretch of iterations in one linear domain has length at most 6βn/ε
-- statement:
--   Let $J$ be a well-formed instance with $n\ge1$ agents whose slopes are all integer powers of $(1+\varepsilon)$, where $0<\varepsilon<1$, and let $\beta$ bound $|\log\lambda|$ for every slope $\lambda$ of $J$. Let $(\pi^k,p^k)_{0\le k\le T}$ be a run of Algorithm 1 with threshold $M$, and let $S=\{i,i+1,\dots,j\}$, $1\le i\le j$, be successive iterations in which the linear domain stays the same, $(L^{i-1},U^{i-1})=(L^i,U^i)=\dots=(L^j,U^j)$, with iteration $j+1$ executed ($j+1\le T$). Then
--   $$|S|=j+1-i\ \le\ \frac{6\beta n}{\varepsilon}.$$
--
--   Combined with the bound on the number of domain changes it yields the polynomial iteration count of Theorem 1.
--
--   **Formalization Note** $\log$ is the natural logarithm, and $\beta$ (the paper's "bit complexity of the input parameters") enters only through $|\log\lambda|\le\beta$. The page uses $\pi^{j+1}$ in its chain $w(\pi^i)<\dots<w(\pi^{j+1})$; the hypothesis $j+1\le T$ states that this iteration exists.
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 13, proof of Theorem 1, inequality (3)

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Inequality (3), proof of Theorem 1, p. 13: for an instance with the powers-of-`(1+ε)`
property, `0 < ε < 1`, and all slopes with `|log λ| ≤ β`, a stretch `S = {i, …, j}` of executed
iterations of Algorithm 1 during which the linear domain stays `(L^{i−1}, U^{i−1})`, followed by
an executed iteration `j + 1`, has length `|S| = j + 1 − i ≤ 6βn/ε`. -/
theorem ineq_3 {n : ℕ} (hn : 1 ≤ n) (J : Instance n) (ε β M : ℝ) (hJ : Standing J)
    (hε : 0 < ε) (hε1 : ε < 1) (hpow : PowersProp ε J)
    (hβ : ∀ a r, ∀ e ∈ (J.v a r).pieces, |Real.log e.2| ≤ β) (hM : IsThreshold J M)
    (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ) (hrun : IsRun J M T π p)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hjT : j + 1 ≤ T)
    (hdom : ∀ k, i ≤ k → k ≤ j →
      domL (hatInst M J) (p k) = domL (hatInst M J) (p (i - 1)) ∧
        domU (hatInst M J) (p k) = domU (hatInst M J) (p (i - 1))) :
    ((j + 1 - i : ℕ) : ℝ) ≤ 6 * β * n / ε := by sorry

end FairRentFPTAS.Approx
