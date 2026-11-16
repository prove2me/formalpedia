-- Prove2me | Theorems.Thm_BordenaveCollins_norm_sum_cfun_mul_trace_Bprod_le
-- name    : BordenaveCollins.norm_sum_cfun_mul_trace_Bprod_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:09:20.944342+00:00
-- url     : https://prove2.me/theorems/bc4cceac-254f-499e-8162-1c18eefa8cbe
-- title:
--   Polynomial growth bound for the first-order sum over a product of linear factors in F_r * Γ_s
-- statement:
--   Let $B_{j,l}$ be a periodic family of $D_m \times D_m$ matrix coefficients (`Lin r s`), with linear factors $X_j = \sum_l B_{j,l} \otimes \lambda(g_l)$ on $D_m$ copies of $\ell^2(F_r * \Gamma_s)$, and suppose $\|X_j\| \le R$ for all $j$, with $R \ge 0$. Then there are a constant $C$ and an exponent $k$ such that for every $m \ge 1$,
--   $$\Big|\sum_{\substack{i_1, \dots, i_m \\ g_{i_1} \cdots g_{i_m} \ne e}} c(g_{i_1} \cdots g_{i_m}) \operatorname{tr}\big(B_{1,i_1} \cdots B_{m,i_m}\big)\Big| \le C\, m^k R^m,$$
--   where each $i_t$ ranges over the identity and the letters $u_i^{\pm1}$, $m_j$, and $c$ is the first-order coefficient `cfun`: $c(g)$ is the number of ways to write $g$ as a reduced product $a z^k a^{-1}$ with $k \ge 2$ and $z \ne e$, minus $1$ if $g$ is an involution.
--
--   This is the estimate of Lemmas 9.5 and 9.6 of Chen, Garza-Vargas, Tropp and van Handel, *A new approach to strong convergence* (first-passage decomposition in the Cayley tree, then Cauchy–Schwarz), with the free group replaced by $F_r * \Gamma_s$; the involutions $a m_j a^{-1}$ have no counterpart there.
--
--   **Formalization note.** The definitions are in the bundle `Def_BordenaveCollins`. The constants $C$ and $k$ may depend on the family $B$ and on $R$. The trace is the full, unnormalized trace over $D_m$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 28-29, Lemmas 9.5 and 9.6, adapted to F_r * Γ_s; a step of our proof of the theorem of Bordenave, C. and Collins, B., Eigenvalues of random lifts and polynomials of random permutation matrices, Ann. of Math. (2) 190 (2019) 811–875, https://doi.org/10.4007/annals.2019.190.3.3

import Mathlib
import Definitions.Def_BordenaveCollins

open scoped Classical

namespace BordenaveCollins

theorem norm_sum_cfun_mul_trace_Bprod_le {r s : ℕ} (L : Lin r s) (R : ℝ) (hR : 0 ≤ R)
    (hX : ∀ j, ‖Xop L j‖ ≤ R) :
    ∃ (C : ℝ) (k : ℕ), ∀ m : ℕ, 1 ≤ m →
      ‖∑ i : Fin m → Option (Lt r s),
          if iprod i = 1 then (0 : ℂ) else (cfun (iprod i) : ℂ) * (Bprod L m i).trace‖ ≤
        C * (m : ℝ) ^ k * R ^ m := by
  sorry

end BordenaveCollins
