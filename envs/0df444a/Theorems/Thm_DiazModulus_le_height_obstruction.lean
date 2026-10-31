-- Prove2me | Theorems.Thm_DiazModulus_le_height_obstruction
-- name    : DiazModulus.le_height_obstruction
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:25.241331+00:00
-- url     : https://prove2.me/theorems/e96ab6b1-a6f4-4d78-b22b-e8e6fd78d743
-- title:
--   The height condition (H*): every prime over the ideal $A$ has height at least $|A_1| + (d - |H| - |J|)$
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $g = (x, y) \in G$, $\sigma_g$ (`torusTransl g`) is the algebra map $X_h \mapsto X_h + x_h$, $Y_i \mapsto y_i Y_i$, $Z_i \mapsto y_i^{-1} Z_i$, so that $\sigma_g f$ takes at $z$ the value of $f$ at $zg$. For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. For $u_j \in \mathbb{C}^{A_0}$, $a_{ji} \in \mathbb{C}^\times$ ($j \in B_1$, $i \in A_1$, $B_1$ finite) and $s \in \mathbb{Z}^{B_1}$, $g_s = (\sum_j s_j u_j, (\prod_j a_{ji}^{s_j})_i) \in G$ (`hmePoint u a s`). For $P \in R$, a subspace $W \subseteq \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$, $m, n \in \mathbb{N}$ and $S \subseteq G$, `obstructionSpan P W u a m n S` is the span of the $\sigma_{g_s v}(D_l P)$ with $|s_j| \le m$, $v \in S$ and $l$ a list of elements of $W$ of length at most $n$. Put $I_r = J_0 + (\text{obstructionSpan}\,P\,W\,u\,a\,(rM_1)\,(rM_0)\,\{1\})$. `torusStab 𝔭` is the stabiliser $\{g \in G : Z_G(\mathfrak{p})\,g \subseteq Z_G(\mathfrak{p})\}$. `sectionIdeal ℓ ψ` is the ideal $J_0 + (\sum_{h'} \ell_{k,h'} X_{h'})_k + (Y^{\psi_k^+} Z^{\psi_k^-} - 1)_k$ of $R$. Let $r \in \mathbb{N}$, $d = |A_0| + |A_1|$, $\mathfrak{p} \supseteq J_0$ a prime such that for every $z \in G$, if $I_r \subseteq \sigma_z^{-1}(\mathfrak{p})$ then $\sigma_z^{-1}(\mathfrak{p})$ (`𝔭.comap (torusTransl z)`) is a minimal prime of $I_r$. For an ideal $\mathfrak{p}$, $F_{\mathfrak{p}}$ = `obstructionSpan P W u a (r M₁) (r M₀) (torusZero 𝔭)` and $A = J_0 + (F_{\mathfrak{p}})$. Let $H \subseteq A_0$, $J \subseteq A_1$, $\ell_h \in \mathbb{C}^{A_0}$, $\psi_i \in \mathbb{Z}^{A_1}$. The forms are normalised off $H$: $\ell_{h,h} = 1$ and $\ell_{h,h'} = 0$ for $h, h' \notin H$, $h' \ne h$; the rows are triangular off $J$: $\psi_{i,i} \ne 0$ and $\psi_{i,i'} = 0$ for $i, i' \notin J$, $i' \ne i$. If `sectionIdeal ℓ ψ` $\subseteq I(\text{torusStab}\,\mathfrak{p})$, then every prime $\mathfrak{q} \supseteq A$ has $\operatorname{ht}\mathfrak{q} \ge |A_1| + (d - (|H| + |J|))$ (truncated subtraction). The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** By `DiazModulus.exists_le_translate_of_le_torusVanishing`, $\mathfrak{a} = $ `sectionIdeal ℓ ψ` lies in some $\sigma_g^{-1}(\mathfrak{q})$, whose quotient has dimension at most $\dim R/\mathfrak{a} \le |H| + |J|$ (`DiazModulus.ringKrullDim_quotient_sectionIdeal_le`); `DiazModulus.card_le_height_add_of_ringKrullDim_quotient_le` gives $|A_0| + 2|A_1| \le \operatorname{ht} + |H| + |J|$, and $\sigma_g$ keeps heights (`DiazModulus.torusTransl_algEquiv`).
--
--   **Novelty.** None claimed: the height condition of §8.4.1 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.4.1 (the height of the primes over $A$). Uses `DiazModulus.exists_le_translate_of_le_torusVanishing`, `DiazModulus.ringKrullDim_quotient_sectionIdeal_le`, `DiazModulus.card_le_height_add_of_ringKrullDim_quotient_le` and `DiazModulus.torusTransl_algEquiv`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem le_height_obstruction {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ)))
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ r : ℕ) (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔭 : 𝔭.IsPrime)
    (hJ𝔭 : torusIdeal ℂ A₀ A₁ ≤ 𝔭)
    (hc : ∀ z : TorusGroup ℂ A₀ A₁, torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ 𝔭.comap (torusTransl z) →
        𝔭.comap (torusTransl z) ∈ (torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))).minimalPrimes)
    (H : Finset A₀) (J : Finset A₁) (ℓ : A₀ → A₀ → ℂ) (ψ : A₁ → A₁ → ℤ)
    (hℓ : ∀ h ∉ H, ℓ h h = 1 ∧ ∀ h' ∉ H, h' ≠ h → ℓ h h' = 0) (hψ : ∀ i ∉ J, ψ i i ≠ 0 ∧ ∀ i' ∉ J, i' ≠ i → ψ i i' = 0)
    (h𝔞 : sectionIdeal ℓ ψ ≤ torusVanishing (torusStab 𝔭)) :
    ∀ p : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ), p.IsPrime → torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ p →
      ((Fintype.card A₁ + ((Fintype.card A₀ + Fintype.card A₁) - (H.card + J.card)) : ℕ) : ℕ∞) ≤ p.height := by
  sorry

end DiazModulus
