-- Prove2me | Theorems.Thm_DiazModulus_wustholz_le_boxHilb
-- name    : DiazModulus.wustholz_le_boxHilb
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:50.366747+00:00
-- url     : https://prove2.me/theorems/2e4a582e-9863-44a7-8ec5-7042ba16098f
-- title:
--   Wüstholz's inequality (8.20) at finite level: if $A$ vanishes to order $> S_0$ along $W$ relative to $J$, then $\binom{S_0 + \ell}{\ell} h_J(T) \le h_A(T + S_0 C)$
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). For $w = (\xi, \eta) \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. For $T \in \mathbb{N}^{A_0 \sqcup A_1}$, `torusBox _ A₀ A₁ T` is the span of the monomials of degree at most $T_h$ in $X_h$ and at most $T_i$ in the pair $Y_i, Z_i$, and $h_I(T)$ (`boxHilb (torusBox ℂ A₀ A₁) I T`) is the dimension of the image of that box in $R/I$. For an ideal $J$ and a subspace $W$, `vanishOrd J W t` is the set of $Q$ with $D_l Q \in J$ for every list $l$ of elements of $W$ of length at most $t$ (vanishing to order $> t$ along $W$ relative to $J$). Let $J$, $A$ be ideals of $R$, $W$ a subspace of $\mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$ and $S_0 \in \mathbb{N}$ with $A \subseteq$ `vanishOrd J W S₀`; let $w_1, \dots, w_n \in W$ and $Q_1, \dots, Q_n \in J$ in a box $C_Q$ with $D_{w_i} Q_j - \delta_{ij} \in J$. Then $\binom{S_0 + n}{n}\, h_J(T) \le h_A(T + S_0 C_Q)$ for every $T$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** With $e_1, \dots, e_h$ in the box $T$ independent modulo $J$, $h = h_J(T)$ (`DiazModulus.exists_boxHilb_family`), the products $e_i Q^\alpha$, $|\alpha| \le S_0$ (`DiazModulus.card_multiIndex` counts them), lie in the box $T + S_0 C_Q$ and are independent modulo $A$: applying $D^\beta$ to a relation and `DiazModulus.derivation_pow_mul_mem` isolate the coefficients of length $|\beta|$, by induction on $|\beta|$. `DiazModulus.card_le_boxHilb_of_linearIndependent` concludes.
--
--   **Novelty.** None claimed: Wüstholz's inequality (8.20) of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), (8.20) (Wüstholz's argument) with Lemmas 8.15 and 8.16. Uses `DiazModulus.derivation_pow_mul_mem`, `DiazModulus.card_multiIndex`, `DiazModulus.card_le_boxHilb_of_linearIndependent`, `DiazModulus.exists_boxHilb_family` and `DiazModulus.restrictSupport_block_filtration`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem wustholz_le_boxHilb {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (J A : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
    (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ))) (S₀ n : ℕ) (hA : (A : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ⊆ vanishOrd J W S₀)
    (w : Fin n → (A₀ → ℂ) × (A₁ → ℂ)) (hw : ∀ i, w i ∈ W) (Q : Fin n → (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (CQ : A₀ ⊕ A₁ → ℕ)
    (hQbox : ∀ j, Q j ∈ torusBox ℂ A₀ A₁ CQ) (hQ : ∀ j, Q j ∈ J)
    (hwQ : ∀ i j, torusDeriv (w i) (Q j) - (if i = j then 1 else 0) ∈ J) (T : A₀ ⊕ A₁ → ℕ) :
    (S₀ + n).choose n * boxHilb (torusBox ℂ A₀ A₁) J T ≤ boxHilb (torusBox ℂ A₀ A₁) A (T + S₀ • CQ) := by
  sorry

end DiazModulus
