-- Prove2me | Theorems.Thm_DiazModulus_torusVanishing_univ
-- name    : DiazModulus.torusVanishing_univ
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:53:06.147697+00:00
-- url     : https://prove2.me/theorems/26167479-be8c-4e1d-8308-ce1f5c916465
-- title:
--   The ideal of $\mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ in $\mathbb{C}[X, Y, Z]$ is the torus ideal $(Y_iZ_i - 1)$, which is prime of height at least $|A_1|$
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. Then $I(G) = J_0$, $J_0$ is prime, and $\operatorname{ht} J_0 \ge |A_1|$. Krull dimensions take values in $\{-\infty\} \cup \mathbb{N} \cup \{\infty\}$ and heights in $\mathbb{N} \cup \{\infty\}$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** If $f$ vanishes on $G$, shifting exponents gives a polynomial $q$ with $q \prod_i Y_i$ vanishing everywhere, so $q = 0$, and $f \equiv \prod_i Z_i^N q = 0$ modulo $J_0$. $I(G)$ is the ideal of the image of $(x, u) \mapsto (x, e^u, e^{-u})$, prime by `DiazModulus.isPrime_iInf_ker_eval_of_analytic`; the height is `DiazModulus.le_height_torusVanishing`.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical: the ideal of the torus $\mathbb{G}_a^{d_0} \times \mathbb{G}_m^{d_1}$ in its coordinate ring. Uses `DiazModulus.isPrime_iInf_ker_eval_of_analytic` and `DiazModulus.le_height_torusVanishing`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem torusVanishing_univ {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] :
    torusVanishing (Set.univ : Set (TorusGroup ℂ A₀ A₁)) = torusIdeal ℂ A₀ A₁ ∧ (torusIdeal ℂ A₀ A₁).IsPrime ∧
      (Fintype.card A₁ : ℕ∞) ≤ (torusIdeal ℂ A₀ A₁).height := by
  sorry

end DiazModulus
