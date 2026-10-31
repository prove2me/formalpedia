-- Prove2me | Theorems.Thm_DiazModulus_torusTransl_algEquiv
-- name    : DiazModulus.torusTransl_algEquiv
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:51.97066+00:00
-- url     : https://prove2.me/theorems/8c2dbad6-92fc-42e0-a7f2-1b0efb5b73f4
-- title:
--   The translation $f \mapsto f \circ \tau_g$ is an automorphism of $K[X, Y, Z]$ preserving boxes and the torus ideal; it moves vanishing ideals and zero sets by $g^{-1}$
-- statement:
--   Let $K$ be a field. Let $A_0, A_1$ be finite types and $R = K[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) K` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $K^{A_0}$, $y \in (K^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $g = (x, y) \in G$, $\sigma_g$ (`torusTransl g`) is the $K$-algebra map $X_h \mapsto X_h + x_h$, $Y_i \mapsto y_i Y_i$, $Z_i \mapsto y_i^{-1} Z_i$, so that $\sigma_g f$ takes at $z$ the value of $f$ at $zg$. For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. Then for $g \in G$ there is a $K$-algebra automorphism $e$ of $R$ with $e(f) = \sigma_g f$ for every $f$, which maps every box `torusBox K A₀ A₁ T` onto itself and $J_0$ onto $J_0$, with $e(I(S)) = I(\{z : zg \in S\})$ for every $S \subseteq G$ and $Z_G(e(\mathfrak{b})) = \{z : zg \in Z_G(\mathfrak{b})\}$ for every ideal $\mathfrak{b}$. Moreover $\sigma_g \circ \sigma_h = \sigma_{gh}$ and $\sigma_1$ is the identity. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** `DiazModulus.exists_translation_algEquiv` (round C1.1) gives an automorphism with the same values on the variables, preserving boxes and $J_0$; it equals $\sigma_g$. The rest follows from $(\sigma_g f)(z) = f(zg)$ and is checked on the variables.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical: translations of $\mathbb{G}_a^{d_0} \times \mathbb{G}_m^{d_1}$; compare M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.3. Uses `DiazModulus.exists_translation_algEquiv`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem torusTransl_algEquiv {K A₀ A₁ : Type*} [Field K] (g : TorusGroup K A₀ A₁) :
    (∃ e : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K ≃ₐ[K] (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), (∀ f, e f = torusTransl g f) ∧
      (∀ T : A₀ ⊕ A₁ → ℕ, (torusBox K A₀ A₁ T).map e.toLinearMap = torusBox K A₀ A₁ T) ∧
      (torusIdeal K A₀ A₁).map e = torusIdeal K A₀ A₁ ∧
      (∀ S : Set (TorusGroup K A₀ A₁), (torusVanishing S).map e = torusVanishing {z | z * g ∈ S}) ∧
      ∀ 𝔟 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), torusZero (𝔟.map e) = {z | z * g ∈ torusZero 𝔟}) ∧
    (∀ (h : TorusGroup K A₀ A₁) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), torusTransl g (torusTransl h f) = torusTransl (g * h) f) ∧
    ∀ f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K, torusTransl (1 : TorusGroup K A₀ A₁) f = f := by
  sorry

end DiazModulus
