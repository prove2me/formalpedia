-- Prove2me | Theorems.Thm_DiazModulus_exists_le_translate_of_le_torusVanishing
-- name    : DiazModulus.exists_le_translate_of_le_torusVanishing
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:13.697799+00:00
-- url     : https://prove2.me/theorems/2e548e2f-00f6-46fb-8ba1-e1b663e3310f
-- title:
--   Every prime over the ideal $A$ contains a translate of any ideal $\mathfrak{a}$ vanishing on the stabiliser of $Z(\mathfrak{p})$
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $w = (\xi, \eta) \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. For $g = (x, y) \in G$, $\sigma_g$ (`torusTransl g`) is the algebra map $X_h \mapsto X_h + x_h$, $Y_i \mapsto y_i Y_i$, $Z_i \mapsto y_i^{-1} Z_i$, so that $\sigma_g f$ takes at $z$ the value of $f$ at $zg$. For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. For $u_j \in \mathbb{C}^{A_0}$, $a_{ji} \in \mathbb{C}^\times$ ($j \in B_1$, $i \in A_1$, $B_1$ finite) and $s \in \mathbb{Z}^{B_1}$, $g_s = (\sum_j s_j u_j, (\prod_j a_{ji}^{s_j})_i) \in G$ (`hmePoint u a s`). For $P \in R$, a subspace $W \subseteq \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$, $m, n \in \mathbb{N}$ and $S \subseteq G$, `obstructionSpan P W u a m n S` is the span of the $\sigma_{g_s v}(D_l P)$ with $|s_j| \le m$, $v \in S$ and $l$ a list of elements of $W$ of length at most $n$. Put $I_r = J_0 + (\text{obstructionSpan}\,P\,W\,u\,a\,(rM_1)\,(rM_0)\,\{1\})$. `torusStab 𝔭` is the stabiliser $\{g \in G : Z_G(\mathfrak{p})\,g \subseteq Z_G(\mathfrak{p})\}$. Let $r \in \mathbb{N}$ and $\mathfrak{p} \supseteq J_0$ a prime such that for every $z \in G$, if $I_r \subseteq \sigma_z^{-1}(\mathfrak{p})$ then $\sigma_z^{-1}(\mathfrak{p})$ (`𝔭.comap (torusTransl z)`) is a minimal prime of $I_r$. For an ideal $\mathfrak{p}$, $F_{\mathfrak{p}}$ = `obstructionSpan P W u a (r M₁) (r M₀) (torusZero 𝔭)` and $A = J_0 + (F_{\mathfrak{p}})$. Let $\mathfrak{a} \subseteq I(\text{torusStab}\,\mathfrak{p})$ be an ideal and $\mathfrak{q} \supseteq A$ a prime. Then $\mathfrak{a} \subseteq \sigma_g^{-1}(\mathfrak{q})$ for some $g \in G$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** For $z \in Z_G(A)$, $I_r \subseteq \sigma_z^{-1}(\mathfrak{p})$ (`DiazModulus.torusVanishing_torusZero`, `DiazModulus.torusTransl_algEquiv`), one of the finitely many minimal primes of $I_r$; points giving the same prime differ by the stabiliser. So finitely many translates of $\mathfrak{a}$ have their intersection in $\sqrt{A} \subseteq \mathfrak{q}$, and prime avoidance picks one.
--
--   **Novelty.** None claimed: the finiteness of the cosets in §8.4.1 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.4.1 (the zero set of $A$ meets finitely many cosets of the stabiliser). Uses `DiazModulus.torusVanishing_torusZero` and `DiazModulus.torusTransl_algEquiv`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem exists_le_translate_of_le_torusVanishing {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ)))
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ r : ℕ) (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔭 : 𝔭.IsPrime)
    (hJ𝔭 : torusIdeal ℂ A₀ A₁ ≤ 𝔭)
    (hc : ∀ z : TorusGroup ℂ A₀ A₁, torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ 𝔭.comap (torusTransl z) →
        𝔭.comap (torusTransl z) ∈ (torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))).minimalPrimes)
    (𝔞 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔞 : 𝔞 ≤ torusVanishing (torusStab 𝔭)) (𝔮 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔮 : 𝔮.IsPrime)
    (hA𝔮 : torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ 𝔮) :
    ∃ g : TorusGroup ℂ A₀ A₁, 𝔞 ≤ 𝔮.comap (torusTransl g) := by
  sorry

end DiazModulus
