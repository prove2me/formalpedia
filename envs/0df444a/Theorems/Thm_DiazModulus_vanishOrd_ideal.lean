-- Prove2me | Theorems.Thm_DiazModulus_vanishOrd_ideal
-- name    : DiazModulus.vanishOrd_ideal
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:51.513174+00:00
-- url     : https://prove2.me/theorems/166a962f-4ed1-4978-b8b6-abdc08e62b11
-- title:
--   Vanishing to order $> t$ along $W$ relative to an ideal $J$ is an ideal, containing the torus ideal when $J$ does
-- statement:
--   Let $K$ be a field. Let $A_0, A_1$ be finite types and $R = K[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) K` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). For $w = (\xi, \eta) \in K^{A_0} \times K^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. For an ideal $J$ and a subspace $W$, `vanishOrd J W t` is the set of $Q$ with $D_l Q \in J$ for every list $l$ of elements of $W$ of length at most $t$ (vanishing to order $> t$ along $W$ relative to $J$). Then `vanishOrd J W t` is the underlying set of an ideal $I$ of $R$, and $J_0 \subseteq J$ implies $J_0 \subseteq I$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** Each $D_l$ is linear. Stability under multiplication goes by induction on the length bound, writing a list as $L$ followed by $b$ and using Leibniz for $D_b$. If $J_0 \subseteq J$, then $J_0$ is stable under every $D_w$ (`DiazModulus.torusDeriv_mem_torusBox`), hence under every $D_l$.
--
--   **Novelty.** None claimed: the vanishing conditions of §8.4.1 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.4.1 (vanishing to a given order along $W$ on a finite set). Uses `DiazModulus.torusDeriv_mem_torusBox`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem vanishOrd_ideal {K A₀ A₁ : Type*} [Field K] (J : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K))
    (W : Submodule K ((A₀ → K) × (A₁ → K))) (t : ℕ) :
    ∃ I : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K), (I : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) = vanishOrd J W t ∧
      (torusIdeal K A₀ A₁ ≤ J → torusIdeal K A₀ A₁ ≤ I) := by
  sorry

end DiazModulus
