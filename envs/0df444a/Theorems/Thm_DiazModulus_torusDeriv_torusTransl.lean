-- Prove2me | Theorems.Thm_DiazModulus_torusDeriv_torusTransl
-- name    : DiazModulus.torusDeriv_torusTransl
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:40.787328+00:00
-- url     : https://prove2.me/theorems/84414e93-06f1-457b-a615-8eda57aebd89
-- title:
--   The invariant derivations commute with the translations of $\mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$: $D_w(f \circ \tau_g) = (D_w f) \circ \tau_g$
-- statement:
--   Let $K$ be a field. Let $A_0, A_1$ be finite types and $R = K[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) K` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $K^{A_0}$, $y \in (K^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $w = (\xi, \eta) \in K^{A_0} \times K^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. For $g = (x, y) \in G$, $\sigma_g$ (`torusTransl g`) is the $K$-algebra map $X_h \mapsto X_h + x_h$, $Y_i \mapsto y_i Y_i$, $Z_i \mapsto y_i^{-1} Z_i$, so that $\sigma_g f$ takes at $z$ the value of $f$ at $zg$. Then $D_w(\sigma_g f) = \sigma_g(D_w f)$ for every $w$, every $g \in G$ and every $f \in R$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** Induction on $f$: both sides are additive and kill constants, and the Leibniz rule reduces the claim to the variables, where $D_w(X_h + x_h) = \xi_h$, $D_w(y_iY_i) = y_i\eta_iY_i$ and $D_w(y_i^{-1}Z_i) = -y_i^{-1}\eta_iZ_i$.
--
--   **Novelty.** None claimed: the translation invariance (8.10) of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), Lemma 8.11 and (8.10): $D(P) \circ \tau_g = D(P \circ \tau_g)$. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem torusDeriv_torusTransl {K A₀ A₁ : Type*} [Field K] (w : (A₀ → K) × (A₁ → K)) (g : TorusGroup K A₀ A₁)
    (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) :
    torusDeriv w (torusTransl g f) = torusTransl g (torusDeriv w f) := by
  sorry

end DiazModulus
