-- Prove2me | Theorems.Thm_DiazModulus_exists_chain_prime
-- name    : DiazModulus.exists_chain_prime
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:01.014846+00:00
-- url     : https://prove2.me/theorems/ba7c777f-e333-404b-849e-951f4ac2ba8a
-- title:
--   The descent of DALAG 8.4.1: some step $r < d$ of the chain $I_r$ has a common minimal prime $\mathfrak{p}$ with $I_{r+1}$, all of whose translates over $I_r$ are minimal
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $w = (\xi, \eta) \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. For $g = (x, y) \in G$, $\sigma_g$ (`torusTransl g`) is the algebra map $X_h \mapsto X_h + x_h$, $Y_i \mapsto y_i Y_i$, $Z_i \mapsto y_i^{-1} Z_i$, so that $\sigma_g f$ takes at $z$ the value of $f$ at $zg$. For $u_j \in \mathbb{C}^{A_0}$, $a_{ji} \in \mathbb{C}^\times$ ($j \in B_1$, $i \in A_1$, $B_1$ finite) and $s \in \mathbb{Z}^{B_1}$, $g_s = (\sum_j s_j u_j, (\prod_j a_{ji}^{s_j})_i) \in G$ (`hmePoint u a s`). For $P \in R$, a subspace $W \subseteq \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$, $m, n \in \mathbb{N}$ and $S \subseteq G$, `obstructionSpan P W u a m n S` is the span of the $\sigma_{g_s v}(D_l P)$ with $|s_j| \le m$, $v \in S$ and $l$ a list of elements of $W$ of length at most $n$. Put $I_r = J_0 + (\text{obstructionSpan}\,P\,W\,u\,a\,(rM_1)\,(rM_0)\,\{1\})$. Let $P \in R$, $W \subseteq \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$ a subspace, $M_0, M_1 \in \mathbb{N}$, $d = |A_0| + |A_1|$, and assume that $D_l P$ vanishes at $g_s$ for every list $l$ of elements of $W$ of length at most $d M_0$ and every $s$ with $|s_j| \le d M_1$. Assume moreover $P \notin J_0$. Then there are $r < d$ and a prime $\mathfrak{p} \supseteq J_0$ with $P \in \mathfrak{p}$ such that (b) $\sigma_{g_s}(D_l P) \in \mathfrak{p}$ for $|s_j| \le (r+1) M_1$ and every list $l$ of elements of $W$ of length at most $(r+1) M_0$; (c) for every $z \in G$, if $I_r \subseteq \sigma_z^{-1}(\mathfrak{p})$ then $\sigma_z^{-1}(\mathfrak{p})$ (`𝔭.comap (torusTransl z)`) is a minimal prime of $I_r$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** The heights of $I_0 \subseteq \cdots \subseteq I_d$ satisfy $\operatorname{ht} I_0 \ge |A_1| + 1$ ($P \notin J_0$, $J_0$ prime of height $\ge |A_1|$, `DiazModulus.torusVanishing_univ`) and $\operatorname{ht} I_d \le |A_0| + 2|A_1|$ ($I_d$ vanishes at the point of $1$). So the height stops growing at some $r < d$; a prime $\mathfrak{p} \supseteq I_{r+1}$ of that height gives (b), and (c) follows since $\sigma_z$ preserves heights (`DiazModulus.torusTransl_algEquiv`).
--
--   **Novelty.** None claimed: the descent of §8.4.1 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.4.1 (the chain of ideals and the choice of $\mathfrak{p}$). Uses `DiazModulus.torusTransl_algEquiv` and `DiazModulus.torusVanishing_univ`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem exists_chain_prime {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (hP0 : P ∉ torusIdeal ℂ A₀ A₁)
    (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ))) (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ : ℕ)
    (hvan : ∀ l : List ((A₀ → ℂ) × (A₁ → ℂ)), l.length ≤ (Fintype.card A₀ + Fintype.card A₁) * M₀ → (∀ w ∈ l, w ∈ W) →
      ∀ s : B₁ → ℤ, (∀ b, |s b| ≤ (((Fintype.card A₀ + Fintype.card A₁) * M₁ : ℕ) : ℤ)) →
        MvPolynomial.eval (torusPt (hmePoint u a s)) (torusDerivList l P) = 0) :
    ∃ r < (Fintype.card A₀ + Fintype.card A₁), ∃ 𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ), 𝔭.IsPrime ∧ torusIdeal ℂ A₀ A₁ ≤ 𝔭 ∧ P ∈ 𝔭 ∧
      (∀ s : B₁ → ℤ, (∀ b, |s b| ≤ (((r + 1) * M₁ : ℕ) : ℤ)) → ∀ l : List ((A₀ → ℂ) × (A₁ → ℂ)), l.length ≤ (r + 1) * M₀ →
        (∀ w ∈ l, w ∈ W) → torusTransl (hmePoint u a s) (torusDerivList l P) ∈ 𝔭) ∧
      ∀ z : TorusGroup ℂ A₀ A₁, torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ 𝔭.comap (torusTransl z) →
        𝔭.comap (torusTransl z) ∈ (torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))).minimalPrimes := by
  sorry

end DiazModulus
