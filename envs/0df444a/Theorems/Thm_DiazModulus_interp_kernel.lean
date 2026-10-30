-- Prove2me | Theorems.Thm_DiazModulus_interp_kernel
-- name    : DiazModulus.interp_kernel
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:29.572336+00:00
-- url     : https://prove2.me/theorems/e68feeba-df9e-4502-b32e-53bb00f34e14
-- title:
--   Th. 11.21 Steps 3–5: if $C\,\Xi \le L^{1/\dim V}$, the interpolation matrix has a nonzero kernel vector, i.e. the vanishing premise of the multiplicity estimate
-- statement:
--   Points are $p = (p', p'') \in \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ for finite index sets $\iota_0, \iota_1$. For $w = (w', w'')$ and a weight vector $t$ on $\iota_1$, $\mathrm{Op}^t_w$ is the operator $\sum_{h \in \iota_0} w'_h\,\partial/\partial X_h + \sum_{i \in \iota_1} w''_i t_i$ on polynomials in the $X_h$ ($h \in \iota_0$), and for vectors $w_k$ ($k \in \kappa_0$) and $k_1, \dots, k_r \in \kappa_0$, $\mathrm{Op}^t_{w,k} = \mathrm{Op}^t_{w_{k_1}} \cdots \mathrm{Op}^t_{w_{k_r}}$ (the factors commute). For $T_0, T_1 \geq 1$ the columns are the $\lambda = (\tau, t)$ with $\tau \in \{0, \dots, T_0\}^{\iota_0}$ and $t \in \{-T_1, \dots, T_1\}^{\iota_1}$; there are $L = (T_0 + 1)^{|\iota_0|}(2T_1 + 1)^{|\iota_1|}$ of them. Given $u_j \in \mathbb{C}^{\iota_0}$ and $a_{ji} \in \mathbb{C}$ ($j \in \kappa_1$, $i \in \iota_1$), the entry at a row datum $(r, k, s)$ ($r \in \mathbb{N}$, $k_1, \dots, k_r \in \kappa_0$, $s \in \mathbb{Z}^{\kappa_1}$) and a column $(\tau, t)$ is $E_{(r,k,s),(\tau,t)} = (\mathrm{Op}^t_{w,k} X^\tau)(\sum_j s_j u_j) \cdot \prod_i (\prod_j a_{ji}^{s_j})^{t_i}$. In the entries, $u_j = \eta'_j$ and $a_{ji} = e^{\eta''_{j,i}}$, for points $\eta_j = (\eta'_j, \eta''_j)$. Let $V \subseteq \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ be a subspace of dimension $n \geq 1$ containing every $w_k$ and every $\eta_j$, and suppose the coordinates of the $w_k$ and of the $\eta'_j$ are algebraic and every $\eta''_{j,i}$ lies in $\mathcal{L}$. Then there is $C > 0$ such that, for all $T_0, T_1 \geq 1$ and $N_0, N_1 \in \mathbb{N}$ with $C \Xi \leq L^{1/n}$, where $\Xi = N_0 \log(T_0 + T_1 + 2) + T_0 \log(N_1 + 2) + T_1(N_1 + 1)$, some non-zero vector $c$ on the columns satisfies $\sum_\lambda c_\lambda E_{(r,k,s),\lambda} = 0$ for every $r \leq N_0$, every $k_1, \dots, k_r$ and every $s$ with $|s_j| \leq N_1$. This is the premise of the multiplicity estimate.
--
--   **Proof.** Index the rows by the finite set of row data with $r \leq N_0$ and $|s_j| \leq N_1$. If some maximal minor $\Delta$ were non-zero, `DiazModulus.interp_det_liouville` would give $\log |\Delta| \geq -C_{10} L \Xi$ and `DiazModulus.interp_det_upper` $|\Delta| \leq \exp(-(\Theta_n(L) - LN_0) + C_9 L \Xi)$, so $\Theta_n(L) \leq LN_0 + (C_9 + C_{10}) L \Xi$. With $A = \lfloor L^{1/n}/2 \rfloor$, $2A^n \leq L$, and `DiazModulus.thetaN_ge_mul_sub` gives $AL \leq 2\Theta_n(L)$; as $1 \leq \Xi$ and $N_0 \leq \Xi$, the hypothesis with $C = 8 + 4(C_9 + C_{10})$ excludes this. So every maximal minor vanishes, and `DiazModulus.exists_ne_zero_mulVec_eq_zero_of_minors` gives the kernel vector.
--
--   **Novelty.** Classical; routine formalisation. Steps 3–5 of the proof of DALAG Th. 11.21 (the interpolation determinant).
-- source:
--   Steps 3–5 of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (the linear subgroup theorem; proof in §11.7.1). Uses DiazModulus.thetaN_ge_mul_sub, DiazModulus.interp_det_upper, DiazModulus.interp_det_liouville and DiazModulus.exists_ne_zero_mulVec_eq_zero_of_minors. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem interp_kernel {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (V : Submodule ℂ ((ι₀ → ℂ) × (ι₁ → ℂ))) (hV : 1 ≤ Module.finrank ℂ ↥V)
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hwV : ∀ k, w k ∈ V) (hwalg : ∀ k, (∀ h, (w k).1 h ∈ Qbar) ∧ ∀ i, (w k).2 i ∈ Qbar)
    (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hηV : ∀ j, η j ∈ V) (hηalg : ∀ j, (∀ h, (η j).1 h ∈ Qbar) ∧ ∀ i, (η j).2 i ∈ LogAlg) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ T₁ N₀ N₁ : ℕ, 1 ≤ T₀ → 1 ≤ T₁ →
      C * ((N₀ : ℝ) * Real.log ((T₀ : ℝ) + T₁ + 2) + (T₀ : ℝ) * Real.log ((N₁ : ℝ) + 2)
          + (T₁ : ℝ) * ((N₁ : ℝ) + 1))
        ≤ (((T₀ + 1) ^ Fintype.card ι₀ * (2 * T₁ + 1) ^ Fintype.card ι₁ : ℕ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℂ ↥V) →
      ∃ c : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → ℂ, c ≠ 0 ∧
        ∀ (rₑ : ℕ) (kₑ : Fin rₑ → κ₀) (sₑ : κ₁ → ℤ), rₑ ≤ N₀ → (∀ j, |sₑ j| ≤ ((N₁ : ℕ) : ℤ)) →
        ∑ l, c l * (MvPolynomial.eval (∑ j, ((sₑ j : ℤ) : ℂ) • (fun j => (η j).1) j)
          ((List.ofFn fun k : Fin rₑ =>
            ((∑ h, (w (kₑ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (kₑ k)).2 i * (((l.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
        * ∏ i, (∏ j, (fun j i => Complex.exp ((η j).2 i)) j i ^ sₑ j) ^ (((l.2 i : ℕ) : ℤ) - T₁)) = 0 := by
  sorry

end DiazModulus
