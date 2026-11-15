-- Prove2me | Theorems.Thm_DiazModulus_roy_rat_adapted_basis
-- name    : DiazModulus.roy_rat_adapted_basis
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:33.094599+00:00
-- url     : https://prove2.me/theorems/903b6f72-a8ba-47bb-af15-b46a03ff7bef
-- title:
--   A subspace S ⊆ ℂᵈ spanned by rational vectors becomes {v : vᵢ = 0 for i ≥ dim S} after a change of coordinates g with g and g⁻¹ mapping Mᵈ into Mᵈ for every ℚ-subspace M of ℂ
-- statement:
--   A vector of $\mathbb C^d$ is *rational* if its coordinates are rational numbers, and a subspace $S \subseteq \mathbb C^d$ is *rational over $\mathbb Q$* if it is spanned by its rational vectors.
--
--   Let $S \subseteq \mathbb C^d$ be rational over $\mathbb Q$. Then there is a $\mathbb C$-linear automorphism $g$ of $\mathbb C^d$ such that, for every $\mathbb Q$-vector subspace $M \subseteq \mathbb C$, both $g$ and $g^{-1}$ map $M^d$ into $M^d$, and $v \in S$ if and only if $(gv)_i = 0$ for every index $i \ge \dim S$ (the indices run over $0, \dots, d - 1$).
-- source:
--   Classical linear algebra over ℚ ⊆ ℂ, used in the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 11.15 (p. 398), for (ℚ, ℚ + ℒ); the analogue over ℚ of DiazModulus.roy_rational_adapted_basis. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_rat_adapted_basis {d : ℕ} (S : Submodule ℂ (Fin d → ℂ))
    (hS : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = S) :
    ∃ g : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ),
      (∀ (M : Submodule ℚ ℂ) (v : Fin d → ℂ), (∀ i, v i ∈ M) →
        (∀ i, g v i ∈ M) ∧ ∀ i, g.symm v i ∈ M) ∧
      ∀ v : Fin d → ℂ, v ∈ S ↔ ∀ i : Fin d, Module.finrank ℂ ↥S ≤ i.val → g v i = 0 := by
  sorry

end DiazModulus
