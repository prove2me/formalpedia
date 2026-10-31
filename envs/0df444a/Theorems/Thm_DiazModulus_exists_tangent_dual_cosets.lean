-- Prove2me | Theorems.Thm_DiazModulus_exists_tangent_dual_cosets
-- name    : DiazModulus.exists_tangent_dual_cosets
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:08.968677+00:00
-- url     : https://prove2.me/theorems/21e8a5f3-7e71-43ab-b9bc-d99ae08c502a
-- title:
--   Lemma 8.15 at finite level: dual pairs on a subgroup $\Gamma$ with comaximal cosets extend to the finite union of cosets $\Sigma \cdot \Gamma$, inside a box
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $w = (\xi, \eta) \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. For $u_j \in \mathbb{C}^{A_0}$, $a_{ji} \in \mathbb{C}^\times$ ($j \in B_1$, $i \in A_1$, $B_1$ finite) and $s \in \mathbb{Z}^{B_1}$, $g_s = (\sum_j s_j u_j, (\prod_j a_{ji}^{s_j})_i) \in G$ (`hmePoint u a s`). For $T \in \mathbb{N}^{A_0 \sqcup A_1}$, `torusBox _ A₀ A₁ T` is the span of the monomials of degree at most $T_h$ in $X_h$ and at most $T_i$ in the pair $Y_i, Z_i$, and $h_I(T)$ (`boxHilb (torusBox ℂ A₀ A₁) I T`) is the dimension of the image of that box in $R/I$. Let $\Gamma$ be a subgroup of $G$. The cosets of $\Gamma$ are comaximal: $I(\Gamma g^{-1}) + I(\Gamma g'^{-1}) = R$ whenever $g g'^{-1} \notin \Gamma$, where $\Gamma g^{-1} = \{z : zg \in \Gamma\}$. $\Sigma \cdot S = \{g_s \gamma : |s_j| \le M_1,\ \gamma \in S\}$ for $S \subseteq G$. Let $M_1 \in \mathbb{N}$, $w_1, \dots, w_n \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$ and $P_1, \dots, P_n \in I(\Gamma)$ with $D_{w_i} P_j - \delta_{ij} \in I(\Gamma)$. Then there are $Q_1, \dots, Q_n$ and $C_Q \in \mathbb{N}^{A_0 \sqcup A_1}$ with every $Q_j$ in the box $C_Q$, $Q_j \in I(\Sigma \cdot \Gamma)$ and $D_{w_i} Q_j - \delta_{ij} \in I(\Sigma \cdot \Gamma)$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** $\Sigma \cdot \Gamma$ lies in finitely many cosets of $\Gamma$, whose ideals are pairwise comaximal; the Chinese remainder theorem gives $B_c \equiv 1$ on the coset $c$ and $B_c = 0$ on the others. Put $Q_j = \sum_c B_c^2\,\sigma_{r_c} P_j$; Leibniz and `DiazModulus.torusDeriv_torusTransl` give the congruences, and `DiazModulus.restrictSupport_block_filtration` a box.
--
--   **Novelty.** None claimed: Lemma 8.15 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), Lemma 8.15. Uses `DiazModulus.torusDeriv_torusTransl` and `DiazModulus.restrictSupport_block_filtration`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem exists_tangent_dual_cosets {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (Γ : Subgroup (TorusGroup ℂ A₀ A₁))
    (hcop : ∀ g g' : TorusGroup ℂ A₀ A₁, g * g'⁻¹ ∉ Γ →
      torusVanishing {z | z * g ∈ Γ} ⊔ torusVanishing {z | z * g' ∈ Γ} = ⊤)
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₁ n : ℕ) (w : Fin n → (A₀ → ℂ) × (A₁ → ℂ)) (P : Fin n → (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
    (hP : ∀ j, P j ∈ torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁)))
    (hwP : ∀ i j, torusDeriv (w i) (P j) - (if i = j then 1 else 0) ∈ torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))) :
    ∃ (Q : Fin n → (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (CQ : A₀ ⊕ A₁ → ℕ), (∀ j, Q j ∈ torusBox ℂ A₀ A₁ CQ) ∧
      (∀ j, Q j ∈ torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ}) ∧
      ∀ i j, torusDeriv (w i) (Q j) - (if i = j then 1 else 0) ∈ torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ} := by
  sorry

end DiazModulus
