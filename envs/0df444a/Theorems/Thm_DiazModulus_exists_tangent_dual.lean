-- Prove2me | Theorems.Thm_DiazModulus_exists_tangent_dual
-- name    : DiazModulus.exists_tangent_dual
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:25.611534+00:00
-- url     : https://prove2.me/theorems/4c04aecb-e39f-4aa8-a92c-2248134642e3
-- title:
--   Lemma 8.14 at finite level: on a set inside $V \times T_\psi$ there are $w_i \in W$ and $P_j$ vanishing there with $D_{w_i} P_j \equiv \delta_{ij}$, $\ell = \dim W - \dim(W \cap V \times L)$
-- statement:
--   Let $K$ be a field. Let $A_0, A_1$ be finite types and $R = K[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) K` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $K^{A_0}$, $y \in (K^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $w = (\xi, \eta) \in K^{A_0} \times K^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. For $S \subseteq G$, $I(S)$ (`torusVanishing S`) is the ideal of the polynomials vanishing at every point of $S$; for an ideal $\mathfrak{b}$, $Z_G(\mathfrak{b})$ (`torusZero 𝔟`) is the set of $g \in G$ at which every element of $\mathfrak{b}$ vanishes. For a subspace $V \subseteq K^{A_0}$ and integer rows $\psi_k \in \mathbb{Z}^{A_1}$, `standardSet V ψ` is $\{(x, y) \in G : x \in V,\ \prod_i y_i^{\psi_{k,i}} = 1 \text{ for every } k\}$, the subgroup $V \times T_\psi$. Let $\ell_h \in K^{A_0}$ ($h \in A_0$), $\psi_i \in \mathbb{Z}^{A_1}$ ($i \in A_1$), $V = \{v : \sum_{h'} \ell_{h,h'} v_{h'} = 0 \text{ for every } h\}$, $L = \{v \in K^{A_1} : \sum_{i'} \psi_{i,i'} v_{i'} = 0 \text{ for every } i\}$, $W$ a subspace of $K^{A_0} \times K^{A_1}$ and $S \subseteq V \times T_\psi$. Then there are $n \in \mathbb{N}$, $w_1, \dots, w_n \in W$ and $P_1, \dots, P_n \in I(S)$ with $n + \dim(W \cap (V \times L)) = \dim W$ and $D_{w_i} P_j - \delta_{ij} \in I(S)$ for all $i, j$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** Let $\beta(\xi, \eta) = ((\sum_{h'} \ell_{h,h'}\xi_{h'})_h, (\sum_{i'} \psi_{i,i'}\eta_{i'})_i)$, whose kernel is $V \times L$. On the span of the forms $\sum_{h'} \ell_{h,h'} X_{h'}$ and the $Y^{\psi_k^+}Z^{\psi_k^-} - 1$, which vanish on $S$, $D_w$ acts modulo $I(S)$ by the constants of $\beta(w)$. Dual bases of $\beta(W)$ give the $w_i$ and $P_j$, and rank–nullity gives $n$.
--
--   **Novelty.** None claimed: Lemma 8.14 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), Lemma 8.14. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem exists_tangent_dual {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁] (ℓ : A₀ → A₀ → K) (ψ : A₁ → A₁ → ℤ)
    (V : Submodule K (A₀ → K)) (L : Submodule K (A₁ → K))
    (hV : ∀ v, v ∈ V ↔ ∀ h, ∑ h', ℓ h h' * v h' = 0) (hL : ∀ v, v ∈ L ↔ ∀ i, ∑ i', (ψ i i' : K) * v i' = 0)
    (W : Submodule K ((A₀ → K) × (A₁ → K))) (S : Set (TorusGroup K A₀ A₁)) (hS : S ⊆ standardSet V ψ) :
    ∃ (n : ℕ) (w : Fin n → (A₀ → K) × (A₁ → K)) (P : Fin n → (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)),
      n + Module.finrank K ↥(W ⊓ V.prod L) = Module.finrank K ↥W ∧ (∀ i, w i ∈ W) ∧
      (∀ j, P j ∈ torusVanishing S) ∧
      ∀ i j, torusDeriv (w i) (P j) - (if i = j then 1 else 0) ∈ torusVanishing S := by
  sorry

end DiazModulus
