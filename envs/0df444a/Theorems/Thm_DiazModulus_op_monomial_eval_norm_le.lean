-- Prove2me | Theorems.Thm_DiazModulus_op_monomial_eval_norm_le
-- name    : DiazModulus.op_monomial_eval_norm_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:49.24999+00:00
-- url     : https://prove2.me/theorems/14b1d3e4-359d-4d09-a28b-cc0b8ad2e84d
-- title:
--   $|(\mathrm{Op}_{w_1} \cdots \mathrm{Op}_{w_r} X^\tau)(p)| \le (H(|\tau| + \sum_i |t_i| + 1))^r P^{|\tau|}$ if the $w$ have entries $\le H$ and $p$ has coordinates $\le P$
-- statement:
--   Points are $p = (p', p'') \in \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ for finite index sets $\iota_0, \iota_1$. For $w = (w', w'')$ and a weight vector $t$ on $\iota_1$, $\mathrm{Op}^t_w$ is the operator $\sum_{h \in \iota_0} w'_h\,\partial/\partial X_h + \sum_{i \in \iota_1} w''_i t_i$ on polynomials in the $X_h$ ($h \in \iota_0$), and for vectors $w_k$ ($k \in \kappa_0$) and $k_1, \dots, k_r \in \kappa_0$, $\mathrm{Op}^t_{w,k} = \mathrm{Op}^t_{w_{k_1}} \cdots \mathrm{Op}^t_{w_{k_r}}$ (the factors commute). Here the weights $t \in \mathbb{C}^{\iota_1}$ may be complex. Suppose every coordinate of every $w_k$ has absolute value at most $H$, with $H \geq 0$; every coordinate of $p \in \mathbb{C}^{\iota_0}$ has absolute value at most $P$, with $P \geq 1$; and $\sum_i |t_i| \leq t_b$. Then for $r \in \mathbb{N}$, $k_1, \dots, k_r \in \kappa_0$ and $\tau \in \mathbb{N}^{\iota_0}$, $|(\mathrm{Op}^t_{w,k} X^\tau)(p)| \leq (H(|\tau| + t_b + 1))^r P^{|\tau|}$, where $|\tau| = \sum_h \tau_h$.
--
--   **Proof.** By induction on $r$, for all exponents at once, peeling off the last operator. One operator sends $X^s$ to $\sum_h w'_h s_h X^{s - e_h} + c X^s$ with $|c| = |\sum_i w''_i t_i| \leq H t_b$. The remaining operators are linear, so the induction hypothesis bounds each term; $s - e_h$ lies below $s$, and $P \geq 1$, $H \geq 0$ make the bound increase with $|s|$. Summing gives $H(|s| + t_b)B \leq H(|s| + t_b + 1)B$. The base case is $|p^s| \leq P^{|s|}$.
--
--   **Novelty.** Not found in the sources read in this form; routine. An elementary size bound, used in Step 4 of the proof of DALAG Th. 11.21.
-- source:
--   An elementary estimate for Step 4 of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (the linear subgroup theorem; proof in §11.7.1). Not found in the sources read in this form; routine. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem op_monomial_eval_norm_le {ι₀ ι₁ κ₀ : Type} [Fintype ι₀] [Fintype ι₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (Hw : ℝ) (hHw : 0 ≤ Hw)
    (hw : ∀ k, (∀ h, ‖(w k).1 h‖ ≤ Hw) ∧ ∀ i, ‖(w k).2 i‖ ≤ Hw)
    (p : ι₀ → ℂ) (P : ℝ) (hP : 1 ≤ P) (hp : ∀ h, ‖p h‖ ≤ P)
    (t : ι₁ → ℂ) (tb : ℝ) (ht : ∑ i, ‖t i‖ ≤ tb) (r : ℕ) (κ : Fin r → κ₀) (τ : ι₀ → ℕ) :
    ‖MvPolynomial.eval p ((List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ k)).2 i * t i) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
          (∏ h, MvPolynomial.X h ^ τ h))‖
      ≤ (Hw * ((∑ h, τ h : ℕ) + tb + 1)) ^ r * P ^ (∑ h, τ h) := by
  sorry

end DiazModulus
