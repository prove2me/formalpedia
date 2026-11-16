-- Prove2me | Theorems.Thm_BordenaveCollins_exists_linearization
-- name    : BordenaveCollins.exists_linearization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:09:57.117343+00:00
-- url     : https://prove2.me/theorems/71731183-6e26-4441-b967-ddf905fbc658
-- title:
--   Linearization of a matrix-coefficient element of ℂ[F_r * Γ_s], with the traces of the coefficients of its powers
-- statement:
--   Let $x \in M_D(\mathbb C) \otimes \mathbb C[F_r * \Gamma_s]$ and $\delta > 0$, and write $\|x\|$ for the norm of $x$ in the left-regular representation. Then there are $q \ge 1$, a size $D_m$ and $D_m \times D_m$ matrices $B_{j,l}$, periodic in $j$ with period $q$ and indexed by $l$ ranging over the identity and the letters $u_i^{\pm1}$, $m_j$, such that the linear factors $X_j = \sum_l B_{j,l} \otimes \lambda(g_l)$ satisfy
--   $$\|X_j\| \le (\|x\| + \delta)^{1/q} \quad\text{for all } j,$$
--   and for every $p \ge 1$ and every group element $g$,
--   $$\operatorname{tr}\big((x^p)_g\big) = \sum_{i_1, \dots, i_{pq}\,:\; g_{i_1} \cdots g_{i_{pq}} = g} \operatorname{tr}\big(B_{1,i_1} B_{2,i_2} \cdots B_{pq,i_{pq}}\big),$$
--   where $(x^p)_g \in M_D(\mathbb C)$ is the coefficient of $g$ in $x^p$ and the traces are not normalized.
--
--   This combines Lemma 9.1 (Pisier's linearization) and the expansion behind Lemma 9.2 of Chen, Garza-Vargas, Tropp and van Handel, *A new approach to strong convergence*, with the free group replaced by $F_r * \Gamma_s$.
--
--   **Formalization note.** The definitions (`MG`, `regOp`, `Lin`, `Xop`, `Bprod`, `iprod`) are in the bundle `Def_BordenaveCollins`. The left side is a trace over $D$ and the right side a trace over $D_m$; the statement does not say how the two sizes are related.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 27, Lemmas 9.1 and 9.2, adapted to F_r * Γ_s; a step of our proof of the theorem of Bordenave, C. and Collins, B., Eigenvalues of random lifts and polynomials of random permutation matrices, Ann. of Math. (2) 190 (2019) 811–875, https://doi.org/10.4007/annals.2019.190.3.3

import Mathlib
import Definitions.Def_BordenaveCollins

open scoped Classical

namespace BordenaveCollins

theorem exists_linearization {r s : ℕ} {D : ℕ} (x : MG D r s) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : Lin r s, (∀ j, ‖Xop L j‖ ≤ (‖regOp x‖ + δ) ^ (1 / (L.q : ℝ))) ∧
      ∀ p : ℕ, 1 ≤ p → ∀ g : G r s,
        Matrix.trace ((x ^ p).coeff g) =
          ∑ i : Fin (p * L.q) → Option (Lt r s),
            if iprod i = g then (Bprod L (p * L.q) i).trace else 0 := by
  sorry

end BordenaveCollins
