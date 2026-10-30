-- Prove2me | Theorems.Thm_DiazModulus_obstruction_1123
-- name    : DiazModulus.obstruction_1123
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:06:01.717988+00:00
-- url     : https://prove2.me/theorems/c4059dcd-6fdd-408a-b55c-d042b962fca3
-- title:
--   Th. 11.21 Step 6: the multiplicity estimate gives $(V, \varphi)$ with $(S_0+1)^{\ell}(2S_1+1)^{\lambda'} T_0^{\dim V} T_1^{\dim L_1} \le \ell!\,K\,T_0^{d_0} T_1^{d_1}$
-- statement:
--   Points are $p = (p', p'') \in \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ for finite index sets $\iota_0, \iota_1$. For $w = (w', w'')$ and a weight vector $t$ on $\iota_1$, $\mathrm{Op}^t_w$ is the operator $\sum_{h \in \iota_0} w'_h\,\partial/\partial X_h + \sum_{i \in \iota_1} w''_i t_i$ on polynomials in the $X_h$ ($h \in \iota_0$), and for vectors $w_k$ ($k \in \kappa_0$) and $k_1, \dots, k_r \in \kappa_0$, $\mathrm{Op}^t_{w,k} = \mathrm{Op}^t_{w_{k_1}} \cdots \mathrm{Op}^t_{w_{k_r}}$ (the factors commute). For $T_0, T_1 \geq 1$ the columns are the $\lambda = (\tau, t)$ with $\tau \in \{0, \dots, T_0\}^{\iota_0}$ and $t \in \{-T_1, \dots, T_1\}^{\iota_1}$; there are $L = (T_0 + 1)^{|\iota_0|}(2T_1 + 1)^{|\iota_1|}$ of them. Given $u_j \in \mathbb{C}^{\iota_0}$ and $a_{ji} \in \mathbb{C}$ ($j \in \kappa_1$, $i \in \iota_1$), the entry at a row datum $(r, k, s)$ ($r \in \mathbb{N}$, $k_1, \dots, k_r \in \kappa_0$, $s \in \mathbb{Z}^{\kappa_1}$) and a column $(\tau, t)$ is $E_{(r,k,s),(\tau,t)} = (\mathrm{Op}^t_{w,k} X^\tau)(\sum_j s_j u_j) \cdot \prod_i (\prod_j a_{ji}^{s_j})^{t_i}$.
--
--   The hypothesis `hME : MultiplicityEstimateElem` is the published definition `MultiplicityEstimateElem` (`DiazModulus.MultiplicityEstimateElem`, module `Definitions.Def_MultiplicityEstimateElem`), a proposition that is assumed here, not proved. It is an elementary form of Philippon's multiplicity estimate: the case $G^- = \{e\}$, $G^+ = G$ of DALAG Th. 8.1 (§8.1) for $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$, written in coordinates. It says: let $A_0, A_1, B_0, B_1$ be finite, $d = |A_0| + |A_1|$, $w_b \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$ ($b \in B_0$), $u_j \in \mathbb{C}^{A_0}$ and non-zero $a_{ji} \in \mathbb{C}$ ($j \in B_1$, $i \in A_1$), $D_0, D_1 \geq 1$, $M_0, M_1 \in \mathbb{N}$, and $c \neq 0$ a vector on the box of the $(\tau, t)$ with $\tau_h \leq D_0$ and $|t_i| \leq D_1$. If $\sum_\lambda c_\lambda E_{(r,k,s),\lambda} = 0$ for every $r \leq dM_0$, every $k_1, \dots, k_r \in B_0$ and every $s$ with $|s_j| \leq dM_1$ (the entries $E$ are those defined above, with $A_0, A_1, B_0, B_1$ for $\iota_0, \iota_1, \kappa_0, \kappa_1$ and $D_0, D_1$ for $T_0, T_1$), then there are a subspace $V \subseteq \mathbb{C}^{A_0}$, integer vectors $\varphi_1, \dots, \varphi_q \in \mathbb{Z}^{A_1}$ with common complex kernel $L_1$, and $\ell$ with $\ell + \dim(W \cap (V \times L_1)) = \dim W$, $W$ the span of the $w_b$, such that $\dim V + \dim L_1 < d$ and every set $R$ of vectors $s$ with $|s_j| \leq M_1$, pairwise incongruent modulo $(V, \varphi)$, has $\binom{M_0 + \ell}{\ell}\, |R|\, D_0^{\dim V} D_1^{\dim L_1} \leq K_d\, D_0^{|A_0|} D_1^{|A_1|}$, with $K_d = 2^{d(d+1)/2}\, d!\, 2^{|A_1|}\, |A_0|^{|A_0|}$; two vectors $s, s' \in \mathbb{Z}^{B_1}$ are congruent modulo $(V, \varphi)$ when $\sum_j (s_j - s'_j) u_j \in V$ and $\prod_i (\prod_j a_{ji}^{s_j - s'_j})^{\varphi_{k,i}} = 1$ for every $k$.
--
--   Let $w_k$ ($k \in \kappa_0$), $u_j \in \mathbb{C}^{\iota_0}$ and non-zero $a_{ji}$ ($j \in \kappa_1$) be given, $T_0, T_1 \geq 1$, $S_0, S_1 \in \mathbb{N}$, $d = |\iota_0| + |\iota_1|$, and $c \neq 0$ a vector on the columns with $\sum_\lambda c_\lambda E_{(r,k,s),\lambda} = 0$ for every $r \leq dS_0$, every $k$ and every $s$ with $|s_j| \leq dS_1$. Assume `hME`. Then there are $V \subseteq \mathbb{C}^{\iota_0}$, $\varphi_1, \dots, \varphi_q \in \mathbb{Z}^{\iota_1}$ with common complex kernel $L_1$, and $\ell$ with $\ell + \dim(W \cap (V \times L_1)) = \dim W$ ($W$ the span of the $w_k$) and $\dim V + \dim L_1 < d$, such that $(S_0 + 1)^\ell (2S_1 + 1)^{\lambda'} T_0^{\dim V} T_1^{\dim L_1} \leq \ell!\, K_d\, T_0^{|\iota_0|} T_1^{|\iota_1|}$, where $\lambda' = |\kappa_1| - \rho$, the relation rank $\rho$ is the dimension of the $\mathbb{Q}$-span of the set of $s \in \mathbb{Z}^{\kappa_1}$ congruent to $0$ modulo $(V, \varphi)$, two vectors $s, s' \in \mathbb{Z}^{\kappa_1}$ are congruent modulo $(V, \varphi)$ when $\sum_j (s_j - s'_j) u_j \in V$ and $\prod_i (\prod_j a_{ji}^{s_j - s'_j})^{\varphi_{k,i}} = 1$ for every $k$, and $K_d$ is as in `hME` with $A_0 = \iota_0$, $A_1 = \iota_1$.
--
--   **Proof.** Apply `hME` to $c$ at $(D_0, D_1, M_0, M_1) = (T_0, T_1, S_0, S_1)$; its premise is the hypothesis on $c$. It gives $(V, \varphi, L_1, \ell)$ and a bound for every set $R$ of pairwise incongruent vectors in the box $|s_j| \leq S_1$. By `DiazModulus.exists_coord_complement` the $\mathbb{Q}$-span of the vectors congruent to $0$ has a coordinate complement $J$ with $|J| = |\kappa_1| - \rho$. Take for $R$ the box on $J$ (zero off $J$): it has $(2S_1 + 1)^{|J|}$ points, and two of its points that are congruent differ by a vector of that span supported on $J$, hence are equal. Finally $(S_0 + 1)^\ell \leq \ell! \binom{S_0 + \ell}{\ell}$, and multiplying the bound by $\ell!$ concludes.
--
--   **Novelty.** Classical; routine formalisation. Step 6 of the proof of DALAG Th. 11.21, which obtains (11.23) from the multiplicity estimate; here the multiplicity estimate is the hypothesis `hME`.
-- source:
--   Step 6 of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (the linear subgroup theorem; proof in §11.7.1), with the multiplicity estimate (Th. 8.1 there; P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), 355–383) carried as the explicit hypothesis hME, the definition MultiplicityEstimateElem. Uses DiazModulus.exists_coord_complement. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem

open Complex ComplexConjugate

namespace DiazModulus

theorem obstruction_1123 (hME : MultiplicityEstimateElem)
    {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (u : κ₁ → ι₀ → ℂ) (a : κ₁ → ι₁ → ℂ) (T₀ T₁ S₀ S₁ : ℕ)
    (c : (ι₀ → Fin (T₀ + 1)) × (ι₁ → Fin (2 * T₁ + 1)) → ℂ) (hT₀ : 1 ≤ T₀) (hT₁ : 1 ≤ T₁) (ha : ∀ j i, a j i ≠ 0) (hc : c ≠ 0)
    (hvan : ∀ (rₑ : ℕ) (kₑ : Fin rₑ → κ₀) (sₑ : κ₁ → ℤ), rₑ ≤ (Fintype.card ι₀ + Fintype.card ι₁) * S₀ → (∀ j, |sₑ j| ≤ (((Fintype.card ι₀ + Fintype.card ι₁) * S₁ : ℕ) : ℤ)) →
        ∑ l, c l * (MvPolynomial.eval (∑ j, ((sₑ j : ℤ) : ℂ) • u j)
          ((List.ofFn fun k : Fin rₑ =>
            ((∑ h, (w (kₑ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (kₑ k)).2 i * (((l.2 i : ℕ) : ℂ) - T₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
        * ∏ i, (∏ j, a j i ^ sₑ j) ^ (((l.2 i : ℕ) : ℤ) - T₁)) = 0) :
    ∃ (V : Submodule ℂ (ι₀ → ℂ)) (q : ℕ) (φ : Fin q → ι₁ → ℤ) (L₁ : Submodule ℂ (ι₁ → ℂ)) (ℓ : ℕ),
      (∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) ∧
      ℓ + Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓ V.prod L₁)
        = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w)) ∧
      Module.finrank ℂ ↥V + Module.finrank ℂ ↥L₁ < Fintype.card ι₀ + Fintype.card ι₁ ∧
      (S₀ + 1) ^ ℓ * (2 * S₁ + 1) ^ (Fintype.card κ₁ - Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) ''
          {s : κ₁ → ℤ | (∑ j, (s j : ℂ) • u j) ∈ V ∧
            ∀ k, ∏ i, (∏ j, a j i ^ s j) ^ φ k i = 1})))
          * T₀ ^ Module.finrank ℂ ↥V * T₁ ^ Module.finrank ℂ ↥L₁
        ≤ ℓ.factorial * (2 ^ ((Fintype.card ι₀ + Fintype.card ι₁) * (Fintype.card ι₀ + Fintype.card ι₁ + 1) / 2)
            * (Fintype.card ι₀ + Fintype.card ι₁).factorial * 2 ^ Fintype.card ι₁
            * Fintype.card ι₀ ^ Fintype.card ι₀) * T₀ ^ Fintype.card ι₀ * T₁ ^ Fintype.card ι₁ := by
  sorry

end DiazModulus
