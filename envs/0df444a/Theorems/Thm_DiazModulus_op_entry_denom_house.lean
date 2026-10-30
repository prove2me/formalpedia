-- Prove2me | Theorems.Thm_DiazModulus_op_entry_denom_house
-- name    : DiazModulus.op_entry_denom_house
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:49.765991+00:00
-- url     : https://prove2.me/theorems/46d03092-306b-4869-a2f5-389771912c55
-- title:
--   Over a number field, $b^E$ times an interpolation entry is an algebraic integer of house at most $H^E (|\tau| + |t| + 1)^r (|s| + 1)^{|\tau|}$
-- statement:
--   Let $K$ be a number field, $\iota_0, \iota_1, \kappa_0, \kappa_1$ finite, $w_k \in K^{\iota_0} \times K^{\iota_1}$ ($k \in \kappa_0$), $u_j \in K^{\iota_0}$ and $a_{ji} \in K$ ($j \in \kappa_1$, $i \in \iota_1$), and define $\mathrm{Op}^t_{w,k}$ as for complex points. There are a non-zero algebraic integer $b \in K$ and $H \geq 1$ such that for all $r$, $k_1, \dots, k_r \in \kappa_0$, $s \in \mathbb{Z}^{\kappa_1}$, $\tau \in \mathbb{N}^{\iota_0}$ and $t \in \mathbb{Z}^{\iota_1}$, with $E = r + |\tau| + (\sum_i |t_i|)(\sum_j |s_j|)$ and $e = (\mathrm{Op}^t_{w,k} X^\tau)(\sum_j s_j u_j) \cdot \prod_i (\prod_j a_{ji}^{s_j})^{t_i}$, the number $b^E e$ is an algebraic integer whose house (the largest absolute value of a conjugate) is at most $H^E (|\tau| + \sum_i |t_i| + 1)^r (\sum_j |s_j| + 1)^{|\tau|}$.
--
--   **Proof.** The data (the coordinates of the $w_k$ and $u_j$, the $a_{ji}$ and their inverses) form one finite family, and `Transcendence.exists_denom_house_monomial_le` gives a common denominator $b$ and a bound $H_0$ for their houses. Say $x$ has property $Q(n, B)$ if $b^n x$ is integral of house at most $H_0^n B$; it is stable under sums, products (adding the $n$), integer multiples and raising $n$. By induction on the operators, every coefficient of $\mathrm{Op}^t_{w,k} X^\tau$ has $Q(r, ((|\iota_0| + 1)(|\tau| + |t| + 1))^r)$, with support below $\tau$; evaluation at $\sum_j s_j u_j$ costs $(|s| + 1)$ per degree, over at most $2^{|\tau|}$ monomials; and the product of the $a_{ji}^{s_j t_i}$ has $Q(|t||s|, 1)$. The constants are absorbed into $H = 2H_0(|\iota_0| + 1)$.
--
--   **Novelty.** Not found in the sources read in this form; routine. Denominator and house bookkeeping for Step 5 of the proof of DALAG Th. 11.21.
-- source:
--   Bookkeeping for Liouville's inequality in Step 5 of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (the linear subgroup theorem; proof in §11.7.1). Liouville's inequality: DALAG §3.5 (cf. Exercise 3.8, Prop. 13.8, cited in Step 5). Not found in the sources read in this form; routine. Uses Transcendence.exists_denom_house_monomial_le. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem op_entry_denom_house {K : Type*} [Field K] [NumberField K] {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁]
    [Fintype κ₀] [Fintype κ₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → K) × (ι₁ → K)) (u : κ₁ → ι₀ → K) (a : κ₁ → ι₁ → K) :
    ∃ b : K, b ≠ 0 ∧ IsIntegral ℤ b ∧ ∃ H : ℝ, 1 ≤ H ∧
      ∀ (r : ℕ) (κ : Fin r → κ₀) (s : κ₁ → ℤ) (τ : ι₀ → ℕ) (t : ι₁ → ℤ),
        IsIntegral ℤ (b ^ (r + ∑ h, τ h + (∑ i, (t i).natAbs) * ∑ j, (s j).natAbs) *
            (MvPolynomial.eval (∑ j, (s j : K) • u j) ((List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ k)).2 i * (t i : K)) • LinearMap.id :
                Module.End K (MvPolynomial ι₀ K)))).prod
              (∏ h, MvPolynomial.X h ^ τ h)) * ∏ i, (∏ j, a j i ^ s j) ^ t i)) ∧
        NumberField.house (b ^ (r + ∑ h, τ h + (∑ i, (t i).natAbs) * ∑ j, (s j).natAbs) *
            (MvPolynomial.eval (∑ j, (s j : K) • u j) ((List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ k)).2 i * (t i : K)) • LinearMap.id :
                Module.End K (MvPolynomial ι₀ K)))).prod
              (∏ h, MvPolynomial.X h ^ τ h)) * ∏ i, (∏ j, a j i ^ s j) ^ t i))
          ≤ H ^ (r + ∑ h, τ h + (∑ i, (t i).natAbs) * ∑ j, (s j).natAbs)
            * ((∑ h, τ h : ℕ) + (∑ i, (t i).natAbs : ℕ) + 1 : ℝ) ^ r
            * ((∑ j, (s j).natAbs : ℕ) + 1 : ℝ) ^ (∑ h, τ h) := by
  sorry

end DiazModulus
