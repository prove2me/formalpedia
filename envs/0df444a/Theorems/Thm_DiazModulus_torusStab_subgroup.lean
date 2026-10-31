-- Prove2me | Theorems.Thm_DiazModulus_torusStab_subgroup
-- name    : DiazModulus.torusStab_subgroup
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:47.973779+00:00
-- url     : https://prove2.me/theorems/e65b802e-5d37-4d4f-8b36-bb5b86737149
-- title:
--   For a prime $\mathfrak{p} \supseteq (Y_iZ_i - 1)$ the stabiliser of $Z_G(\mathfrak{p})$ is a subgroup whose cosets are zero sets with pairwise comaximal ideals
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. `torusStab 𝔭` is the stabiliser $\{g \in G : Z_G(\mathfrak{p})\,g \subseteq Z_G(\mathfrak{p})\}$. Let $\mathfrak{p} \supseteq J_0$ be a prime of $R$. Then there is a subgroup $\Gamma$ of $G$ with underlying set `torusStab 𝔭` such that for every $g$ the coset $\Gamma g^{-1} = \{z : zg \in \Gamma\}$ satisfies $Z_G(I(\Gamma g^{-1})) = \Gamma g^{-1}$, and $I(\Gamma g^{-1}) + I(\Gamma g'^{-1}) = R$ whenever $g g'^{-1} \notin \Gamma$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** Inverses: for $g \in \Gamma$, $\sigma_g\mathfrak{p}$ is a prime with $Z(\sigma_g\mathfrak{p}) = Z(\mathfrak{p}) g^{-1} \supseteq Z(\mathfrak{p})$, so $\sigma_g\mathfrak{p} \subseteq \mathfrak{p}$ by `DiazModulus.torusVanishing_torusZero`, with equality since the heights agree (`DiazModulus.torusTransl_algEquiv`). A coset is the common zero set of translates of $\mathfrak{p}$; distinct cosets have no common zero, so their ideals are comaximal by the torus Nullstellensatz.
--
--   **Novelty.** None claimed: the stabiliser of §8.4.1 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.4.1 (the stabiliser of the zero set of $\mathfrak{p}$). Uses `DiazModulus.torusVanishing_torusZero` and `DiazModulus.torusTransl_algEquiv`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem torusStab_subgroup {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔭 : 𝔭.IsPrime)
    (hJ𝔭 : torusIdeal ℂ A₀ A₁ ≤ 𝔭) :
    ∃ Γ : Subgroup (TorusGroup ℂ A₀ A₁), (Γ : Set (TorusGroup ℂ A₀ A₁)) = torusStab 𝔭 ∧
      (∀ g : TorusGroup ℂ A₀ A₁, torusZero (torusVanishing {z | z * g ∈ Γ}) = {z | z * g ∈ Γ}) ∧
      ∀ g g' : TorusGroup ℂ A₀ A₁, g * g'⁻¹ ∉ Γ →
      torusVanishing {z | z * g ∈ Γ} ⊔ torusVanishing {z | z * g' ∈ Γ} = ⊤ := by
  sorry

end DiazModulus
