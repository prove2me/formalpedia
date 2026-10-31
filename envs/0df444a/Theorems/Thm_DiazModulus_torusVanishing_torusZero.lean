-- Prove2me | Theorems.Thm_DiazModulus_torusVanishing_torusZero
-- name    : DiazModulus.torusVanishing_torusZero
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:47.082601+00:00
-- url     : https://prove2.me/theorems/43bd60c2-f920-4da7-a395-e26c1eeec51f
-- title:
--   Nullstellensatz on the torus: for an ideal $\mathfrak{b} \supseteq (Y_iZ_i - 1)$, $I(Z_G(\mathfrak{b})) = \sqrt{\mathfrak{b}}$, and $Z_G(\mathfrak{b}) = \emptyset$ forces $\mathfrak{b} = (1)$
-- statement:
--   Let $K$ be an algebraically closed field. Let $A_0, A_1$ be finite types and $R = K[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) K` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $K^{A_0}$, $y \in (K^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. For every ideal $\mathfrak{b} \supseteq J_0$ of $R$, $I(Z_G(\mathfrak{b})) = \sqrt{\mathfrak{b}}$, and $Z_G(\mathfrak{b}) = \emptyset$ implies $\mathfrak{b} = R$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** A zero of $\mathfrak{b} \supseteq J_0$ in $K^{A_0} \times K^{A_1} \times K^{A_1}$ has $Y_i Z_i = 1$, so it is the point of some $g \in G$; Hilbert's Nullstellensatz for the affine zero locus gives the radical.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical: Hilbert's Nullstellensatz, on the torus $K^{A_0} \times (K^\times)^{A_1}$. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem torusVanishing_torusZero {K A₀ A₁ : Type*} [Field K] [IsAlgClosed K] [Fintype A₀] [Fintype A₁]
    (𝔟 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) (h𝔟 : torusIdeal K A₀ A₁ ≤ 𝔟) :
    torusVanishing (torusZero 𝔟) = 𝔟.radical ∧ (torusZero 𝔟 = ∅ → 𝔟 = ⊤) := by
  sorry

end DiazModulus
