-- Prove2me | Theorems.Thm_DiazModulus_hlow_le_boxHilb
-- name    : DiazModulus.hlow_le_boxHilb
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:18.851228+00:00
-- url     : https://prove2.me/theorems/132e86d8-7e3f-48cb-ae32-162892949080
-- title:
--   The lower side of the multiplicity estimate: $\binom{M_0+\ell}{\ell} |R| D_0^{\dim V} D_1^{\dim L} u^{\dim V + \dim L} \le h_A(u D + C)$ for every $u \ge 1$
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $w = (\xi, \eta) \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. For $u_j \in \mathbb{C}^{A_0}$, $a_{ji} \in \mathbb{C}^\times$ ($j \in B_1$, $i \in A_1$, $B_1$ finite) and $s \in \mathbb{Z}^{B_1}$, $g_s = (\sum_j s_j u_j, (\prod_j a_{ji}^{s_j})_i) \in G$ (`hmePoint u a s`). For an ideal $J$ and a subspace $W$, `vanishOrd J W t` is the set of $Q$ with $D_l Q \in J$ for every list $l$ of elements of $W$ of length at most $t$ (vanishing to order $> t$ along $W$ relative to $J$). $\Sigma \cdot S = \{g_s \gamma : |s_j| \le M_1,\ \gamma \in S\}$ for $S \subseteq G$. For a subspace $V \subseteq K^{A_0}$ and integer rows $\psi_k \in \mathbb{Z}^{A_1}$, `standardSet V ψ` is $\{(x, y) \in G : x \in V,\ \prod_i y_i^{\psi_{k,i}} = 1 \text{ for every } k\}$, the subgroup $V \times T_\psi$. Let $\Gamma$ be a subgroup of $G$. The cosets of $\Gamma$ are comaximal: $I(\Gamma g^{-1}) + I(\Gamma g'^{-1}) = R$ whenever $g g'^{-1} \notin \Gamma$, where $\Gamma g^{-1} = \{z : zg \in \Gamma\}$. $\Gamma$ has coordinate sections $H \subseteq A_0$, $J \subseteq A_1$: every $x \in \mathbb{C}^{A_0}$ agrees on $H$ with some element of the complex span of $\{x_g : g \in \Gamma\}$, and the only $\varphi \in \mathbb{Z}^{A_1}$ vanishing off $J$ with $\prod_i y_{g,i}^{\varphi_i} = 1$ for every $g = (x_g, y_g) \in \Gamma$ is $\varphi = 0$. Let $\ell_h \in \mathbb{C}^{A_0}$, $\psi_i \in \mathbb{Z}^{A_1}$, $V = \{v : \sum_{h'} \ell_{h,h'} v_{h'} = 0 \ \forall h\}$, $L = \{v : \sum_{i'} \psi_{i,i'} v_{i'} = 0 \ \forall i\}$, with $\Gamma \subseteq V \times T_\psi$, $\dim V = |H|$ and $\dim L = |J|$; let $W$ be a subspace and $n$ with $n + \dim(W \cap (V \times L)) = \dim W$; let $M_0, M_1 \in \mathbb{N}$ and $A$ an ideal with $A \subseteq$ `vanishOrd (I(Σ · Γ)) W M₀`. Let $D_0, D_1 \in \mathbb{N}$ and $R_e$ a finite set of $s \in \mathbb{Z}^{B_1}$ with $|s_j| \le M_1$, pairwise incongruent modulo $(V, \psi)$ ($s$, $s'$ are congruent when $\sum_j (s_j - s'_j) u_j \in V$ and $\prod_i (\prod_j a_{ji}^{s_j - s'_j})^{\psi_{k,i}} = 1$ for every $k$). Then there is $C \in \mathbb{N}^{A_0 \sqcup A_1}$ such that, with $d = |A_0| + |A_1|$ and $D$ = `boxD A₀ A₁ D₀ D₁`, $\binom{M_0 + n}{n} |R_e| D_0^{\dim V} D_1^{\dim L}\, t^{d - (d - (\dim V + \dim L))} \le h_A(tD + C)$ for every $t \ge 1$. For $T \in \mathbb{N}^{A_0 \sqcup A_1}$, `torusBox _ A₀ A₁ T` is the span of the monomials of degree at most $T_h$ in $X_h$ and at most $T_i$ in the pair $Y_i, Z_i$, and $h_I(T)$ (`boxHilb (torusBox ℂ A₀ A₁) I T`) is the dimension of the image of that box in $R/I$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** `DiazModulus.exists_tangent_dual` and `DiazModulus.exists_tangent_dual_cosets` give the dual pairs on $\Sigma \cdot \Gamma$, and `DiazModulus.wustholz_le_boxHilb` gives $\binom{M_0 + n}{n} h_{I(\Sigma \cdot \Gamma)}(T) \le h_A(T + M_0 C_Q)$. Incongruent $s \ne s'$ give distinct cosets $\Gamma g_s$, whose ideals $\sigma I(\Gamma)$ (`DiazModulus.torusTransl_algEquiv`) are comaximal: `DiazModulus.exists_card_mul_boxHilb_le_translates` and `DiazModulus.boxHilb_anti` bound $|R_e| h_{I(\Gamma)}$ by $h_{I(\Sigma \cdot \Gamma)}$. Finally `DiazModulus.le_boxHilb_torusVanishing_subgroup` and `DiazModulus.box_ray_lower_bound` bound $h_{I(\Gamma)}(tD)$ below.
--
--   **Novelty.** None claimed: the lower bound of §8.4.1 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.4.1 (the lower bound for the Hilbert function of $A$), with (8.20) and Lemma 8.15. Uses `DiazModulus.exists_tangent_dual`, `DiazModulus.exists_tangent_dual_cosets`, `DiazModulus.wustholz_le_boxHilb`, `DiazModulus.le_boxHilb_torusVanishing_subgroup`, `DiazModulus.exists_card_mul_boxHilb_le_translates`, `DiazModulus.boxHilb_anti`, `DiazModulus.box_ray_lower_bound`, `DiazModulus.restrictSupport_block_filtration` and `DiazModulus.torusTransl_algEquiv`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem hlow_le_boxHilb {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (Γ : Subgroup (TorusGroup ℂ A₀ A₁))
    (hcop : ∀ g g' : TorusGroup ℂ A₀ A₁, g * g'⁻¹ ∉ Γ →
      torusVanishing {z | z * g ∈ Γ} ⊔ torusVanishing {z | z * g' ∈ Γ} = ⊤)
    (H : Finset A₀) (J : Finset A₁) (hH : ∀ x : A₀ → ℂ, ∃ v ∈ Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v}, ∀ h ∈ H, v h = x h)
    (hJ : ∀ φ : A₁ → ℤ, (∀ i ∉ J, φ i = 0) → (∀ g ∈ Γ, ∏ i, g.2 i ^ φ i = 1) → φ = 0)
    (ℓ : A₀ → A₀ → ℂ) (ψ : A₁ → A₁ → ℤ) (V : Submodule ℂ (A₀ → ℂ)) (L : Submodule ℂ (A₁ → ℂ))
    (hV : ∀ v, v ∈ V ↔ ∀ h, ∑ h', ℓ h h' * v h' = 0) (hL : ∀ v, v ∈ L ↔ ∀ i, ∑ i', (ψ i i' : ℂ) * v i' = 0)
    (hΓ : (Γ : Set (TorusGroup ℂ A₀ A₁)) ⊆ standardSet V ψ) (hVH : Module.finrank ℂ ↥V = H.card) (hLJ : Module.finrank ℂ ↥L = J.card)
    (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ))) (n : ℕ) (hn : n + Module.finrank ℂ ↥(W ⊓ V.prod L) = Module.finrank ℂ ↥W)
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ : ℕ) (A : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
    (hA : (A : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ⊆ vanishOrd (torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ}) W M₀) (D₀ D₁ : ℕ) (Rₑ : Finset (B₁ → ℤ))
    (hR : ∀ s ∈ Rₑ, ∀ b, |s b| ≤ (M₁ : ℤ))
    (hRinc : ∀ s ∈ Rₑ, ∀ s' ∈ Rₑ, ((∑ b, ((s b - s' b : ℤ) : ℂ) • u b) ∈ V ∧
      ∀ k, ∏ i, (∏ b, a b i ^ (s b - s' b)) ^ ψ k i = 1) → s = s') :
    ∃ C : A₀ ⊕ A₁ → ℕ, ∀ t : ℕ, 1 ≤ t →
      (M₀ + n).choose n * Rₑ.card * D₀ ^ Module.finrank ℂ ↥V * D₁ ^ Module.finrank ℂ ↥L * t ^ ((Fintype.card A₀ + Fintype.card A₁) - ((Fintype.card A₀ + Fintype.card A₁) - (Module.finrank ℂ ↥V + Module.finrank ℂ ↥L)))
        ≤ boxHilb (torusBox ℂ A₀ A₁) A (t • boxD A₀ A₁ D₀ D₁ + C) := by
  sorry

end DiazModulus
