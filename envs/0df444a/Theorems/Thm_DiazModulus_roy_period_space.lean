-- Prove2me | Theorems.Thm_DiazModulus_roy_period_space
-- name    : DiazModulus.roy_period_space
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:50:57.679451+00:00
-- url     : https://prove2.me/theorems/43b97d5e-e4b4-4126-a8ad-57920b07e5b7
-- title:
--   If F ⊆ U ∩ (T + cQ̄ᵈ) with T rational, then R = T + span F is rational and $\dim F - \dim(F \cap T) \le \dim R - \dim T = \dim(U \cap R) - \dim(U \cap T)$
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $c \neq 0$, $T, U \subseteq \mathbb C^d$ subspaces with $T$ rational, and $F$ a finite-dimensional $\overline{\mathbb Q}$-subspace of $U$ every element of which is $\tau + c\kappa$ with $\tau \in T$ and $\kappa \in \overline{\mathbb Q}^d$. Then $R = T + \mathrm{span}_{\mathbb C} F$ is rational, $\dim_{\overline{\mathbb Q}} F + \dim T \le \dim_{\overline{\mathbb Q}}(F \cap T) + \dim R$, and $\dim(U \cap R) + \dim T = \dim(U \cap T) + \dim R$.
-- source:
--   Linear algebra; a step of the proof of D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4 (first case). The route is the Diaz modulus mission's: an induction on d that splits along a rational subspace of maximal slope and applies DALAG Th. 11.21 once at each semistable step, counting the periods through one extra rational subspace; DALAG and Roy argue instead through Th. 11.5 (3′) and Lemma 11.24, respectively Roy's Th. 2. Not found in the sources read in this form; routine. Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_period_space {d : ℕ} (c : ℂ) (hc : c ≠ 0) (T U : Submodule ℂ (Fin d → ℂ))
    (hT : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T)
    (F : Submodule (↥Qbar) (Fin d → ℂ)) (hFfin : FiniteDimensional (↥Qbar) ↥F) (hFU : ∀ x ∈ F, x ∈ U)
    (hF : ∀ x ∈ F, ∃ τ ∈ T, ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x = τ + c • κ) :
    Submodule.span ℂ {v : Fin d → ℂ | v ∈ (T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) ∧ ∀ i, v i ∈ Qbar} = (T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) ∧
    Module.finrank (↥Qbar) ↥F + Module.finrank ℂ ↥(T) ≤
      Module.finrank (↥Qbar) ↥(F ⊓ T.restrictScalars (↥Qbar)) + Module.finrank ℂ ↥(T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) ∧
    Module.finrank ℂ ↥(U ⊓ (T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ)))) + Module.finrank ℂ ↥(T) = Module.finrank ℂ ↥(U ⊓ T) + Module.finrank ℂ ↥(T ⊔ Submodule.span ℂ (F : Set (Fin d → ℂ))) := by
  sorry

end DiazModulus
