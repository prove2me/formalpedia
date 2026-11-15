-- Prove2me | Theorems.Thm_DiazModulus_roy_rat_period_space
-- name    : DiazModulus.roy_rat_period_space
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:34.393233+00:00
-- url     : https://prove2.me/theorems/6311071d-dbb7-48d5-a414-4b1c3d1976c3
-- title:
--   If F ⊆ U ∩ (T + cℚᵈ) with T rational over ℚ, then R = T + span F is rational over ℚ and dim F − dim(F ∩ T) ≤ dim R − dim T = dim(U ∩ R) − dim(U ∩ T)
-- statement:
--   A vector of $\mathbb C^d$ is *rational* if its coordinates are rational numbers, and a subspace $S \subseteq \mathbb C^d$ is *rational over $\mathbb Q$* if it is spanned by its rational vectors.
--
--   Let $c \neq 0$, let $T, U \subseteq \mathbb C^d$ be subspaces with $T$ rational over $\mathbb Q$, and let $F$ be a finite-dimensional $\mathbb Q$-subspace of $U$ every element of which is $\tau + c\kappa$ with $\tau \in T$ and $\kappa \in \mathbb Q^d$. Then $R = T + \mathrm{span}_{\mathbb C} F$ is rational over $\mathbb Q$, $\dim_{\mathbb Q} F + \dim T \le \dim_{\mathbb Q}(F \cap T) + \dim R$, and $\dim(U \cap R) + \dim T = \dim(U \cap T) + \dim R$.
-- source:
--   Linear algebra; a step of the proof of D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4, over F = ℚ (Remark (i), p. 37, with ℚ + ℒ in place of ℒ̃); the analogue over ℚ of DiazModulus.roy_period_space. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_rat_period_space {d : ℕ} (c : ℂ) (hc : c ≠ 0) (T U : Submodule ℂ (Fin d → ℂ))
    (hT : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = T)
    (F : Submodule ℚ (Fin d → ℂ)) (hFfin : FiniteDimensional ℚ ↥F) (hFU : ∀ x ∈ F, x ∈ U)
    (hF : ∀ x ∈ F, ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, ∃ q : ℚ, κ i = (q : ℂ)) ∧ x = τ + c • κ) :
    Submodule.span ℂ {v : Fin d → ℂ | v ∈ (T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) ∧
        ∀ i, ∃ q : ℚ, v i = (q : ℂ)} = (T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) ∧
    Module.finrank ℚ ↥F + Module.finrank ℂ ↥T ≤
      Module.finrank ℚ ↥(F ⊓ T.restrictScalars ℚ) +
        Module.finrank ℂ ↥(T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) ∧
    Module.finrank ℂ ↥(U ⊓ (T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ)))) + Module.finrank ℂ ↥T =
      Module.finrank ℂ ↥(U ⊓ T) + Module.finrank ℂ ↥(T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) := by
  sorry

end DiazModulus
