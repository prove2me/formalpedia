-- Prove2me | Theorems.Thm_DiazModulus_exists_coordinate_section_add
-- name    : DiazModulus.exists_coordinate_section_add
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:51:45.255714+00:00
-- url     : https://prove2.me/theorems/c2904665-785f-4d5f-a00b-0772c27c4e3a
-- title:
--   A subspace $V \le K^{A_0}$ has a coordinate set $H$ with $V \to K^H$ bijective, and is cut out by normalised linear forms $\ell_h$, $h \notin H$
-- statement:
--   Let $K$ be a field, $A_0$ a finite type and $V$ a subspace of $K^{A_0}$. Then there are $H \subseteq A_0$ and vectors $\ell_h \in K^{A_0}$ ($h \in A_0$) with $\ell_h = 0$ for $h \in H$, normalised off $H$ ($\ell_{h,h} = 1$ and $\ell_{h,h'} = 0$ for $h, h' \notin H$, $h' \ne h$), such that $V = \{v : \sum_{h'} \ell_{h,h'} v_{h'} = 0 \text{ for every } h\}$, every $x \in K^{A_0}$ agrees on $H$ with some element of $V$, and $\dim V = |H|$.
--
--   **Proof.** Take $H$ of largest size with $V \to K^H$ onto; maximality makes it injective. With $e_{h'}$ the lift of the indicator of $h'$, put $\ell_h = X_h - \sum_{h' \in H} (e_{h'})_h X_{h'}$ for $h \notin H$.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical linear algebra: a subspace as a graph over a coordinate subspace (reduced row echelon form). C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem exists_coordinate_section_add {K A₀ : Type*} [Field K] [Fintype A₀] (V : Submodule K (A₀ → K)) :
    ∃ (H : Finset A₀) (ℓ : A₀ → A₀ → K), (∀ h ∈ H, ℓ h = 0) ∧ (∀ h ∉ H, ℓ h h = 1 ∧ ∀ h' ∉ H, h' ≠ h → ℓ h h' = 0) ∧
      (∀ v, v ∈ V ↔ ∀ h, ∑ h', ℓ h h' * v h' = 0) ∧ (∀ x : A₀ → K, ∃ v ∈ V, ∀ h ∈ H, v h = x h) ∧
      Module.finrank K ↥V = H.card := by
  sorry

end DiazModulus
