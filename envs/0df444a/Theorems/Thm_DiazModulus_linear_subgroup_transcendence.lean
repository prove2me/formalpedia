-- Prove2me | Theorems.Thm_DiazModulus_linear_subgroup_transcendence
-- name    : DiazModulus.linear_subgroup_transcendence
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:47.053371+00:00
-- url     : https://prove2.me/theorems/199ac749-9921-49a0-880f-5264eee8ee59
-- title:
--   DALAG Th. 11.21 (d₀ ≤ n) from the elementary multiplicity estimate: some (V′, φ) has ℓ₀′ < d′ and (λ′ + d₁′)(d − n) ≤ d₁(d′ − ℓ₀′)
-- statement:
--   Points are $p = (p', p'') \in \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ for finite index sets $\iota_0, \iota_1$. For $w = (w', w'')$ and a weight vector $t$ on $\iota_1$, $\mathrm{Op}^t_w$ is the operator $\sum_{h \in \iota_0} w'_h\,\partial/\partial X_h + \sum_{i \in \iota_1} w''_i t_i$ on polynomials in the $X_h$ ($h \in \iota_0$), and for vectors $w_k$ ($k \in \kappa_0$) and $k_1, \dots, k_r \in \kappa_0$, $\mathrm{Op}^t_{w,k} = \mathrm{Op}^t_{w_{k_1}} \cdots \mathrm{Op}^t_{w_{k_r}}$ (the factors commute). For $T_0, T_1 \geq 1$ the columns are the $\lambda = (\tau, t)$ with $\tau \in \{0, \dots, T_0\}^{\iota_0}$ and $t \in \{-T_1, \dots, T_1\}^{\iota_1}$; there are $L = (T_0 + 1)^{|\iota_0|}(2T_1 + 1)^{|\iota_1|}$ of them. Given $u_j \in \mathbb{C}^{\iota_0}$ and $a_{ji} \in \mathbb{C}$ ($j \in \kappa_1$, $i \in \iota_1$), the entry at a row datum $(r, k, s)$ ($r \in \mathbb{N}$, $k_1, \dots, k_r \in \kappa_0$, $s \in \mathbb{Z}^{\kappa_1}$) and a column $(\tau, t)$ is $E_{(r,k,s),(\tau,t)} = (\mathrm{Op}^t_{w,k} X^\tau)(\sum_j s_j u_j) \cdot \prod_i (\prod_j a_{ji}^{s_j})^{t_i}$.
--
--   The hypothesis `hME : MultiplicityEstimateElem` is the published definition `MultiplicityEstimateElem` (`DiazModulus.MultiplicityEstimateElem`, module `Definitions.Def_MultiplicityEstimateElem`), a proposition that is assumed here, not proved. It is an elementary form of Philippon's multiplicity estimate: the case $G^- = \{e\}$, $G^+ = G$ of DALAG Th. 8.1 (§8.1) for $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$, written in coordinates. It says: let $A_0, A_1, B_0, B_1$ be finite, $d = |A_0| + |A_1|$, $w_b \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$ ($b \in B_0$), $u_j \in \mathbb{C}^{A_0}$ and non-zero $a_{ji} \in \mathbb{C}$ ($j \in B_1$, $i \in A_1$), $D_0, D_1 \geq 1$, $M_0, M_1 \in \mathbb{N}$, and $c \neq 0$ a vector on the box of the $(\tau, t)$ with $\tau_h \leq D_0$ and $|t_i| \leq D_1$. If $\sum_\lambda c_\lambda E_{(r,k,s),\lambda} = 0$ for every $r \leq dM_0$, every $k_1, \dots, k_r \in B_0$ and every $s$ with $|s_j| \leq dM_1$ (the entries $E$ are those defined above, with $A_0, A_1, B_0, B_1$ for $\iota_0, \iota_1, \kappa_0, \kappa_1$ and $D_0, D_1$ for $T_0, T_1$), then there are a subspace $V \subseteq \mathbb{C}^{A_0}$, integer vectors $\varphi_1, \dots, \varphi_q \in \mathbb{Z}^{A_1}$ with common complex kernel $L_1$, and $\ell$ with $\ell + \dim(W \cap (V \times L_1)) = \dim W$, $W$ the span of the $w_b$, such that $\dim V + \dim L_1 < d$ and every set $R$ of vectors $s$ with $|s_j| \leq M_1$, pairwise incongruent modulo $(V, \varphi)$, has $\binom{M_0 + \ell}{\ell}\, |R|\, D_0^{\dim V} D_1^{\dim L_1} \leq K_d\, D_0^{|A_0|} D_1^{|A_1|}$, with $K_d = 2^{d(d+1)/2}\, d!\, 2^{|A_1|}\, |A_0|^{|A_0|}$; two vectors $s, s' \in \mathbb{Z}^{B_1}$ are congruent modulo $(V, \varphi)$ when $\sum_j (s_j - s'_j) u_j \in V$ and $\prod_i (\prod_j a_{ji}^{s_j - s'_j})^{\varphi_{k,i}} = 1$ for every $k$.
--
--   Let $d_0 = |\iota_0|$, $d_1 = |\iota_1|$, $d = d_0 + d_1$, and let $V \subseteq \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ be a subspace of dimension $n$ with $1 \leq n < d$ and $d_0 \leq n$. Let $w_k \in V$ ($k \in \kappa_0$) and $\eta_j \in V$ ($j \in \kappa_1$), and suppose the coordinates of the $w_k$ and of the $\eta'_j$ are algebraic and every $\eta''_{j,i}$ lies in $\mathcal{L}$. Assume `hME`. Then there are a subspace $V' \subseteq \mathbb{C}^{\iota_0}$, $\varphi_1, \dots, \varphi_q \in \mathbb{Z}^{\iota_1}$ with common complex kernel $L_1$, and $\ell$ with $\ell + \dim(W \cap (V' \times L_1)) = \dim W$, $W$ the span of the $w_k$, such that $\ell < d'$ and $(\lambda' + d'_1)(d - n) \leq d_1(d' - \ell)$. Here $d'_0 = d_0 - \dim V'$, $d'_1 = d_1 - \dim L_1$, $d' = d'_0 + d'_1$, $\lambda' = |\kappa_1| - \rho$, and $\rho$ is the dimension of the $\mathbb{Q}$-span of the set of $s \in \mathbb{Z}^{\kappa_1}$ with $\sum_j s_j \eta'_j \in V'$ and $\prod_i (\prod_j e^{s_j \eta''_{j,i}})^{\varphi_{k,i}} = 1$ for every $k$.
--
--   This is DALAG Th. 11.21 in the case $d_0 \leq n$, with $W$ the span of algebraic vectors and the obstruction subgroup recorded as $(V', \varphi)$.
--
--   **Proof.** `DiazModulus.interp_kernel` gives a constant $C$. Fix $\nu = (d_0 + n)/(d - n) + 1$ and the curve of `DiazModulus.params_1122_eventually`: $S_0 = \lfloor S_1^{d_1/(d - n)} (\log S_1)^\nu \rfloor$, $T_0 = \lfloor S_0/\log S_1 \rfloor$, $T_1 = \lfloor S_0/S_1 \rfloor$. For all large $S_1$, `DiazModulus.params_1122_eventually` gives $T_0, T_1 \geq 2$ and the constraint of `DiazModulus.interp_kernel` at $(N_0, N_1) = (S_0, S_1)$, so `DiazModulus.interp_kernel` yields $c \neq 0$ whose vanishing covers the premise of `DiazModulus.obstruction_1123` at $(\lfloor S_0/d \rfloor, \lfloor S_1/d \rfloor)$. `DiazModulus.obstruction_1123` returns $(V', \varphi, L_1, \ell)$ with $(\lfloor S_0/d \rfloor + 1)^\ell (2\lfloor S_1/d \rfloor + 1)^{\lambda'} T_0^{\dim V'} T_1^{\dim L_1} \leq \ell!\, K_d\, T_0^{d_0} T_1^{d_1}$; cancelling gives (11.23) with exponents $(\ell, \lambda', d'_0, d'_1)$, and $\ell \leq d'$. These four numbers range over a finite set, so one tuple occurs for infinitely many $S_1$, and `DiazModulus.params_exponents` applied to it gives $\ell < d'$ and $(\lambda' + d'_1)(d - n) \leq d_1(d' - \ell)$.
--
--   **Novelty.** Classical; routine formalisation. DALAG Th. 11.21 (case $d_0 \leq n$), from the multiplicity estimate carried as the hypothesis `hME`. The obstruction is recorded as $(V', \varphi)$, without connectedness or a field of definition, and the $\eta_j$ are not assumed $\mathbb{Z}$-independent; the consumers do not need either.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 11.21 (the linear subgroup theorem; proof in §11.7.1), case d₀ ≤ n, Steps 2–7; the multiplicity estimate (Th. 8.1 there; P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), 355–383) is carried as the explicit hypothesis hME, the definition MultiplicityEstimateElem. Uses DiazModulus.interp_kernel, DiazModulus.obstruction_1123, DiazModulus.params_1122_eventually and DiazModulus.params_exponents. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus
import Definitions.Def_MultiplicityEstimateElem

open Complex ComplexConjugate

namespace DiazModulus

theorem linear_subgroup_transcendence (hME : MultiplicityEstimateElem)
    {ι₀ ι₁ κ₀ κ₁ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype κ₀] [Fintype κ₁]
    [DecidableEq ι₀] [DecidableEq ι₁]
    (V : Submodule ℂ ((ι₀ → ℂ) × (ι₁ → ℂ))) (hV1 : 1 ≤ Module.finrank ℂ ↥V)
    (hVd : Module.finrank ℂ ↥V < Fintype.card ι₀ + Fintype.card ι₁)
    (hd0 : Fintype.card ι₀ ≤ Module.finrank ℂ ↥V)
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hwV : ∀ k, w k ∈ V) (hwalg : ∀ k, (∀ h, (w k).1 h ∈ Qbar) ∧ ∀ i, (w k).2 i ∈ Qbar)
    (η : κ₁ → (ι₀ → ℂ) × (ι₁ → ℂ)) (hηV : ∀ j, η j ∈ V) (hηalg : ∀ j, (∀ h, (η j).1 h ∈ Qbar) ∧ ∀ i, (η j).2 i ∈ LogAlg) :
    ∃ (V' : Submodule ℂ (ι₀ → ℂ)) (q : ℕ) (φ : Fin q → ι₁ → ℤ) (L₁ : Submodule ℂ (ι₁ → ℂ)) (ℓ : ℕ),
      (∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) ∧
      ℓ + Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w) ⊓ V'.prod L₁)
        = Module.finrank ℂ ↥(Submodule.span ℂ (Set.range w)) ∧
      ℓ < (Fintype.card ι₀ - Module.finrank ℂ ↥V' + (Fintype.card ι₁ - Module.finrank ℂ ↥L₁)) ∧
      (Fintype.card κ₁ - Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : κ₁ → ℤ => fun j => (s j : ℚ)) ''
          {s : κ₁ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1}))
          + (Fintype.card ι₁ - Module.finrank ℂ ↥L₁)) * (Fintype.card ι₀ + Fintype.card ι₁ - Module.finrank ℂ ↥V)
        ≤ Fintype.card ι₁ * ((Fintype.card ι₀ - Module.finrank ℂ ↥V' + (Fintype.card ι₁ - Module.finrank ℂ ↥L₁)) - ℓ) := by
  sorry

end DiazModulus
