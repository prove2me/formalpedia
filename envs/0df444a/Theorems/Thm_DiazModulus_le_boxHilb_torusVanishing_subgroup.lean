-- Prove2me | Theorems.Thm_DiazModulus_le_boxHilb_torusVanishing_subgroup
-- name    : DiazModulus.le_boxHilb_torusVanishing_subgroup
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:35.667801+00:00
-- url     : https://prove2.me/theorems/04b78695-3d2a-4068-9288-d76e0cba61d1
-- title:
--   One-minor lower bound: for a subgroup $\Gamma$ with coordinate sections $H$, $J$, $h_{I(\Gamma)}(T) \ge \prod_{h \in H}(T_h + 1) \prod_{j \in J}(2T_j + 1)$
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. For $T \in \mathbb{N}^{A_0 \sqcup A_1}$, `torusBox _ A₀ A₁ T` is the span of the monomials of degree at most $T_h$ in $X_h$ and at most $T_i$ in the pair $Y_i, Z_i$, and $h_I(T)$ (`boxHilb (torusBox ℂ A₀ A₁) I T`) is the dimension of the image of that box in $R/I$. Let $\Gamma$ be a subgroup of $G$. $\Gamma$ has coordinate sections $H \subseteq A_0$, $J \subseteq A_1$: every $x \in \mathbb{C}^{A_0}$ agrees on $H$ with some element of the complex span of $\{x_g : g \in \Gamma\}$, and the only $\varphi \in \mathbb{Z}^{A_1}$ vanishing off $J$ with $\prod_i y_{g,i}^{\varphi_i} = 1$ for every $g = (x_g, y_g) \in \Gamma$ is $\varphi = 0$. Then $\prod_{h \in H} (T_h + 1) \prod_{j \in J} (2T_j + 1) \le h_{I(\Gamma)}(T)$ for every $T$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** The monomials $X_H^a Y_J^{\lambda^+} Z_J^{\lambda^-}$ with $a_h \le T_h$ and $|\lambda_j| \le T_j$ lie in the box and are linearly independent modulo $I(\Gamma)$ by `DiazModulus.linearIndependent_on_subgroup`; `DiazModulus.card_le_boxHilb_of_linearIndependent` counts them.
--
--   **Novelty.** None claimed: the lower bound for the Hilbert function of the obstruction subgroup in §8.4.1 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.4.1 (the Hilbert function of the obstruction subgroup, bounded below). Uses `DiazModulus.linearIndependent_on_subgroup` and `DiazModulus.card_le_boxHilb_of_linearIndependent`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem le_boxHilb_torusVanishing_subgroup {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (Γ : Subgroup (TorusGroup ℂ A₀ A₁)) (H : Finset A₀)
    (J : Finset A₁) (hH : ∀ x : A₀ → ℂ, ∃ v ∈ Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v}, ∀ h ∈ H, v h = x h)
    (hJ : ∀ φ : A₁ → ℤ, (∀ i ∉ J, φ i = 0) → (∀ g ∈ Γ, ∏ i, g.2 i ^ φ i = 1) → φ = 0)
    (T : A₀ ⊕ A₁ → ℕ) :
    (∏ h ∈ H, (T (Sum.inl h) + 1)) * ∏ j ∈ J, (2 * T (Sum.inr j) + 1)
      ≤ boxHilb (torusBox ℂ A₀ A₁) (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))) T := by
  sorry

end DiazModulus
