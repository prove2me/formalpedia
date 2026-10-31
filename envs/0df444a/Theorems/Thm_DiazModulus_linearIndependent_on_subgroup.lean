-- Prove2me | Theorems.Thm_DiazModulus_linearIndependent_on_subgroup
-- name    : DiazModulus.linearIndependent_on_subgroup
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:33.040989+00:00
-- url     : https://prove2.me/theorems/b88ced5b-b45a-4bd6-a3cd-d15ed87e8c85
-- title:
--   On a subgroup $\Gamma$ of $\mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ with coordinate sections $H$, $J$, a reduced polynomial in $X_H, Y_J, Z_J$ vanishing on $\Gamma$ is zero
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). Let $\Gamma$ be a subgroup of $G$. $\Gamma$ has coordinate sections $H \subseteq A_0$, $J \subseteq A_1$: every $x \in \mathbb{C}^{A_0}$ agrees on $H$ with some element of the complex span of $\{x_g : g \in \Gamma\}$, and the only $\varphi \in \mathbb{Z}^{A_1}$ vanishing off $J$ with $\prod_i y_{g,i}^{\varphi_i} = 1$ for every $g = (x_g, y_g) \in \Gamma$ is $\varphi = 0$. Let $f \in R$ be reduced (no monomial of $f$ is divisible by any $Y_iZ_i$; `torusReduced`), with every monomial in the variables $X_h$ ($h \in H$), $Y_j$, $Z_j$ ($j \in J$) only. If $f$ vanishes at every $g \in \Gamma$, then $f = 0$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** On $\Gamma$, $f = \sum_\lambda F_\lambda(x_g)\,y_g^\lambda$ with distinct characters $y^\lambda$ ($\lambda \in \mathbb{Z}^J$). `DiazModulus.eval_eq_zero_of_sum_mul_char` gives $F_\lambda(x_g) = 0$ on $\Gamma$, `DiazModulus.eval_eq_zero_on_span_of_addSubgroup` on the span of the $x_g$, and the section $H$ gives $F_\lambda = 0$.
--
--   **Novelty.** None claimed: the independence used in the lower bound of §8.4.1 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.4.1; the classical independence of characters (Dedekind), applied to the stabiliser. Uses `DiazModulus.eval_eq_zero_of_sum_mul_char` and `DiazModulus.eval_eq_zero_on_span_of_addSubgroup`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem linearIndependent_on_subgroup {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (Γ : Subgroup (TorusGroup ℂ A₀ A₁)) (H : Finset A₀)
    (J : Finset A₁) (hH : ∀ x : A₀ → ℂ, ∃ v ∈ Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v}, ∀ h ∈ H, v h = x h)
    (hJ : ∀ φ : A₁ → ℤ, (∀ i ∉ J, φ i = 0) → (∀ g ∈ Γ, ∏ i, g.2 i ^ φ i = 1) → φ = 0)
    (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (hf : f ∈ MvPolynomial.restrictSupport ℂ (torusReduced A₀ A₁))
    (hfH : ∀ m ∈ f.support, (∀ h ∉ H, m (Sum.inl h) = 0) ∧ ∀ i ∉ J, ∀ b, m (Sum.inr (i, b)) = 0)
    (hΓ : ∀ g ∈ Γ, MvPolynomial.eval (torusPt g) f = 0) :
    f = 0 := by
  sorry

end DiazModulus
