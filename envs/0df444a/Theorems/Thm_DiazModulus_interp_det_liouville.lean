-- Prove2me | Theorems.Thm_DiazModulus_interp_det_liouville
-- name    : DiazModulus.interp_det_liouville
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:27.252613+00:00
-- url     : https://prove2.me/theorems/d32f85c5-8ba3-4c11-9122-06ad008d1c02
-- title:
--   Th. 11.21 Step 5: a nonzero L×L minor of the interpolation matrix with algebraic data is at least exp(−C·L·Ξ) (Liouville)
-- statement:
--   Points are $p = (p', p'') \in \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ for finite index sets $\iota_0, \iota_1$. For $w = (w', w'')$ and a weight vector $t$ on $\iota_1$, $\mathrm{Op}^t_w$ is the operator $\sum_{h \in \iota_0} w'_h\,\partial/\partial X_h + \sum_{i \in \iota_1} w''_i t_i$ on polynomials in the $X_h$ ($h \in \iota_0$), and for vectors $w_k$ ($k \in \kappa_0$) and $k_1, \dots, k_r \in \kappa_0$, $\mathrm{Op}^t_{w,k} = \mathrm{Op}^t_{w_{k_1}} \cdots \mathrm{Op}^t_{w_{k_r}}$ (the factors commute). For $T_0, T_1 \geq 1$ the columns are the $\lambda = (\tau, t)$ with $\tau \in \{0, \dots, T_0\}^{\iota_0}$ and $t \in \{-T_1, \dots, T_1\}^{\iota_1}$; there are $L = (T_0 + 1)^{|\iota_0|}(2T_1 + 1)^{|\iota_1|}$ of them. Given $u_j \in \mathbb{C}^{\iota_0}$ and $a_{ji} \in \mathbb{C}$ ($j \in \kappa_1$, $i \in \iota_1$), the entry at a row datum $(r, k, s)$ ($r \in \mathbb{N}$, $k_1, \dots, k_r \in \kappa_0$, $s \in \mathbb{Z}^{\kappa_1}$) and a column $(\tau, t)$ is $E_{(r,k,s),(\tau,t)} = (\mathrm{Op}^t_{w,k} X^\tau)(\sum_j s_j u_j) \cdot \prod_i (\prod_j a_{ji}^{s_j})^{t_i}$. In the entries, $u_j = \eta'_j$ and $a_{ji} = e^{\eta''_{j,i}}$, for points $\eta_j = (\eta'_j, \eta''_j)$. Suppose the coordinates of the $w_k$ and of the $\eta'_j$ are algebraic and every $\eta''_{j,i}$ lies in $\mathcal{L}$. Then there is $C > 0$ such that, for all $T_0, T_1 \geq 1$ and $N_0, N_1 \in \mathbb{N}$, and for every choice of $L$ row data $(r_\lambda, k_\lambda, s_\lambda)$, one for each column $\lambda$, with $r_\lambda \leq N_0$ and $|s_{\lambda,j}| \leq N_1$, the determinant $\Delta$ of the $L \times L$ matrix $(E_{(r_\lambda, k_\lambda, s_\lambda), \lambda'})_{\lambda, \lambda'}$ satisfies $\log |\Delta| \geq -C L \Xi$ whenever $\Delta \neq 0$, with $\Xi = N_0 \log(T_0 + T_1 + 2) + T_0 \log(N_1 + 2) + T_1(N_1 + 1)$.
--
--   **Proof.** All data are algebraic, so they lie in a number field $F \subseteq \mathbb{C}$, and $\Delta$ is the image of the determinant of the same matrix over $F$. `DiazModulus.op_entry_denom_house` gives $b$ and $H$; with a uniform exponent $E^* = N_0 + |\iota_0| T_0 + |\iota_1| T_1 |\kappa_1| N_1$ every entry of $b^{E^*} M_F$ is integral of bounded house, so $\alpha = \det(b^{E^*} M_F)$ is a non-zero algebraic integer of house at most $L!\, B^L$. Liouville's inequality (`Transcendence.liouville_house`) gives $1 \leq H'^{E^* L} |\Delta| (L!\, B^L)^{[F:\mathbb{Q}] - 1}$; taking logarithms and using $\log L! \leq L \log L$ and elementary bounds gives $\log |\Delta| \geq -CL\Xi$.
--
--   **Novelty.** Classical; routine formalisation. Step 5 of the proof of DALAG Th. 11.21: Liouville's lower bound.
-- source:
--   Step 5 (Liouville's inequality) of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (the linear subgroup theorem; proof in §11.7.1). Liouville's inequality: DALAG §3.5 (cf. Exercise 3.8, Prop. 13.8, cited in Step 5). Uses DiazModulus.op_entry_denom_house and Transcendence.liouville_house. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem interp_det_liouville {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hwalg : ∀ k, (∀ h, (w k).1 h ∈ Qbar) ∧ ∀ i, (w k).2 i ∈ Qbar)
    (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hηalg : ∀ j, (∀ h, (η j).1 h ∈ Qbar) ∧ ∀ i, (η j).2 i ∈ LogAlg) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ T₁ N₀ N₁ : ℕ, 1 ≤ T₀ → 1 ≤ T₁ →
    ∀ (ro : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → ℕ) (ka : (l : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → Fin (ro l) → κ₀)
      (sv : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → κ₁ → ℤ), (∀ l, ro l ≤ N₀) → (∀ l j, |sv l j| ≤ (N₁ : ℤ)) →
      (Matrix.of fun l l' : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) =>
        MvPolynomial.eval (∑ j, (((sv l) j : ℤ) : ℂ) • (fun j => (η j).1) j)
          ((List.ofFn fun k : Fin (ro l) =>
            ((∑ h, (w ((ka l) k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w ((ka l) k)).2 i * (((l'.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l'.1 h : ℕ)))
        * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ (sv l) j) ^ (((l'.2 i : ℕ) : ℤ) - T₁)).det ≠ 0 →
      -(C * (((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ : ℕ) : ℝ) * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1)))
        ≤ Real.log ‖(Matrix.of fun l l' : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) =>
        MvPolynomial.eval (∑ j, (((sv l) j : ℤ) : ℂ) • (fun j => (η j).1) j)
          ((List.ofFn fun k : Fin (ro l) =>
            ((∑ h, (w ((ka l) k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w ((ka l) k)).2 i * (((l'.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l'.1 h : ℕ)))
        * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ (sv l) j) ^ (((l'.2 i : ℕ) : ℤ) - T₁)).det‖ := by
  sorry

end DiazModulus
