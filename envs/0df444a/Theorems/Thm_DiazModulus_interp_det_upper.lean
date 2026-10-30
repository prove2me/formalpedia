-- Prove2me | Theorems.Thm_DiazModulus_interp_det_upper
-- name    : DiazModulus.interp_det_upper
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:20.27416+00:00
-- url     : https://prove2.me/theorems/11e02366-e4b6-4621-b2df-0982b561d6ab
-- title:
--   Th. 11.21 Step 4: an L×L minor of the interpolation matrix is at most exp(−(Θₙ(L) − L·N₀) + C·L·Ξ), n = dim V, by Lemma 9.2 and Schwarz
-- statement:
--   Points are $p = (p', p'') \in \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ for finite index sets $\iota_0, \iota_1$. For $w = (w', w'')$ and a weight vector $t$ on $\iota_1$, $\mathrm{Op}^t_w$ is the operator $\sum_{h \in \iota_0} w'_h\,\partial/\partial X_h + \sum_{i \in \iota_1} w''_i t_i$ on polynomials in the $X_h$ ($h \in \iota_0$), and for vectors $w_k$ ($k \in \kappa_0$) and $k_1, \dots, k_r \in \kappa_0$, $\mathrm{Op}^t_{w,k} = \mathrm{Op}^t_{w_{k_1}} \cdots \mathrm{Op}^t_{w_{k_r}}$ (the factors commute). For $T_0, T_1 \geq 1$ the columns are the $\lambda = (\tau, t)$ with $\tau \in \{0, \dots, T_0\}^{\iota_0}$ and $t \in \{-T_1, \dots, T_1\}^{\iota_1}$; there are $L = (T_0 + 1)^{|\iota_0|}(2T_1 + 1)^{|\iota_1|}$ of them. Given $u_j \in \mathbb{C}^{\iota_0}$ and $a_{ji} \in \mathbb{C}$ ($j \in \kappa_1$, $i \in \iota_1$), the entry at a row datum $(r, k, s)$ ($r \in \mathbb{N}$, $k_1, \dots, k_r \in \kappa_0$, $s \in \mathbb{Z}^{\kappa_1}$) and a column $(\tau, t)$ is $E_{(r,k,s),(\tau,t)} = (\mathrm{Op}^t_{w,k} X^\tau)(\sum_j s_j u_j) \cdot \prod_i (\prod_j a_{ji}^{s_j})^{t_i}$. In the entries, $u_j = \eta'_j$ and $a_{ji} = e^{\eta''_{j,i}}$, for points $\eta_j = (\eta'_j, \eta''_j)$. Let $V \subseteq \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ be a subspace of dimension $n$ containing every $w_k$ ($k \in \kappa_0$) and every $\eta_j$ ($j \in \kappa_1$). Then there is $C > 0$ such that, for all $T_0, T_1 \geq 1$ and $N_0, N_1 \in \mathbb{N}$, and for every choice of $L$ row data $(r_\lambda, k_\lambda, s_\lambda)$, one for each column $\lambda$, with $r_\lambda \leq N_0$ and $|s_{\lambda,j}| \leq N_1$, the determinant $\Delta$ of the $L \times L$ matrix $(E_{(r_\lambda, k_\lambda, s_\lambda), \lambda'})_{\lambda, \lambda'}$ satisfies $|\Delta| \leq \exp(-(\Theta_n(L) - L N_0) + C L \Xi)$, with $\Xi = N_0 \log(T_0 + T_1 + 2) + T_0 \log(N_1 + 2) + T_1(N_1 + 1)$ and $\Theta_n(L)$ is the least value of $\sum_l |\kappa'(l)|$ over the injective maps $\kappa' : \{1, \dots, L\} \to \mathbb{N}^n$, with $|\cdot|$ the total degree of a multi-index ($0$ if there is no such map).
--
--   **Proof.** Fix a basis of $V$ and let $\psi : \mathbb{C}^n \to V$ be the coordinate map. Each column gives the entire function $f_\lambda \circ \psi$, $f_\lambda(z) = z'^\tau e^{\langle t, z'' \rangle}$, and each row the point $\psi^{-1}(\sum_j s_j \eta_j)$ and the directions $\psi^{-1}(w_k)$. By `DiazModulus.iteratedFDeriv_expMono_eq_op` the entries of $F(z) = \det(D^{r}(f \circ \psi)(z\zeta)(v))$ are the polynomial parts at $zp'$ times $e^{z\langle t, p'' \rangle}$, so $F(1) = \Delta$ up to transposition. `DiazModulus.interpolation_det_order` (DALAG Lemma 9.2) gives $\mathrm{ord}_0 F \geq \Theta_n(L) - L N_0$, and `DiazModulus.schwarz_order_at_zero` (Schwarz) with $R = e$ gives $|\Delta| \leq e^{-\mathrm{ord}} \sup_{|z| = e} |F|$. On $|z| = e$ each entry is at most $e^\beta$, by `DiazModulus.op_monomial_eval_norm_le` for the polynomial part and $|e^u| \leq e^{|u|}$, so $|F| \leq L!\, e^{L\beta}$; finally $\log L + \beta \leq K\Xi$ is elementary.
--
--   **Novelty.** Classical; routine formalisation. Step 4 of the proof of DALAG Th. 11.21: the analytic upper bound.
-- source:
--   Step 4 (upper bound) of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (the linear subgroup theorem; proof in §11.7.1); compare Lemma 9.2; Schwarz's lemma is Lemma 2.4. Uses DiazModulus.interpolation_det_order, DiazModulus.schwarz_order_at_zero, DiazModulus.iteratedFDeriv_expMono_eq_op and DiazModulus.op_monomial_eval_norm_le. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem interp_det_upper {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (V : Submodule ℂ ((ι₀ → ℂ) × (ι₁ → ℂ))) (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hwV : ∀ k, w k ∈ V)
    (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hηV : ∀ j, η j ∈ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ T₁ N₀ N₁ : ℕ, 1 ≤ T₀ → 1 ≤ T₁ →
    ∀ (ro : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → ℕ) (ka : (l : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1))) → Fin (ro l) → κ₀)
      (sv : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → κ₁ → ℤ), (∀ l, ro l ≤ N₀) → (∀ l j, |sv l j| ≤ (N₁ : ℤ)) →
      ‖(Matrix.of fun l l' : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) =>
        MvPolynomial.eval (∑ j, (((sv l) j : ℤ) : ℂ) • (fun j => (η j).1) j)
          ((List.ofFn fun k : Fin (ro l) =>
            ((∑ h, (w ((ka l) k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w ((ka l) k)).2 i * (((l'.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l'.1 h : ℕ)))
        * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ (sv l) j) ^ (((l'.2 i : ℕ) : ℤ) - T₁)).det‖
        ≤ Real.exp (-(((sInf {S | ∃ κ' : Fin ((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁) → (Fin (Module.finrank ℂ ↥V) → ℕ), Function.Injective κ' ∧ S = ∑ l, ∑ i, κ' l i} : ℕ) : ℝ)
              - (((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ : ℕ) : ℝ) * N₀)
            + C * (((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ : ℕ) : ℝ) * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1))) := by
  sorry

end DiazModulus
