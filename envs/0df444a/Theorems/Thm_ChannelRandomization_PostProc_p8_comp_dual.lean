-- Prove2me | Theorems.Thm_ChannelRandomization_PostProc_p8_comp_dual
-- name    : ChannelRandomization.PostProc.p8_comp_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:38.577789+00:00
-- url     : https://prove2.me/theorems/12fb9ddd-c9c5-444a-a7dd-a6c3cef0f5e2
-- title:
--   p. 8, paragraph after Example 2 — P*∘P, P∘P* ⊂ P*∩CP
-- statement:
--   Let $\mathcal P$ be an admissible family of positive cones and $\mathcal A,\mathcal B,\mathcal C$ C*-algebras. Then
--
--   1. if $\phi\in\mathcal P(\mathcal A,\mathcal B)$ and $\psi\in\mathcal P^*(\mathcal B,\mathcal C)$, then $\psi\circ\phi\in\mathcal P^*(\mathcal A,\mathcal C)$ and $\psi\circ\phi$ is completely positive;
--   2. if $\psi\in\mathcal P^*(\mathcal A,\mathcal B)$ and $\phi\in\mathcal P(\mathcal B,\mathcal C)$, then $\phi\circ\psi\in\mathcal P^*(\mathcal A,\mathcal C)$ and $\phi\circ\psi$ is completely positive.
--
--   In short, $\mathcal P^*\circ\mathcal P,\ \mathcal P\circ\mathcal P^*\subseteq\mathcal P^*\cap CP$. This is the composition rule used in Theorem 3 to keep payoff maps inside the dual cone: $\Phi\circ\Gamma\in\mathcal P^*(\mathcal D,\mathcal B)$ and $\Gamma\circ\phi\in\mathcal P^*(\mathcal B,\mathcal A)$.
--
--   **Formalization Note.** The page states the inclusion for the families over Hilbert spaces; the Lean statement is the version over C*-algebras (block labels), which is the form used on pp. 15–16. Taking all three labels constant gives the page's Hilbert-space version. The page also says that $\mathcal P^*$ satisfies properties (i) and (iii) of Definition 1; that clause is not part of this statement.
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, p. 8, first paragraph (after Example 2)

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace ChannelRandomization.PostProc
theorem p8_comp_dual (P : AdmissibleFamily) {h k l : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ)
    (C : Fin l → ℕ) :
    (∀ φ ∈ coneOn P A B, ∀ ψ ∈ dualCone P B C, ψ ∘ₗ φ ∈ dualCone P A C ∧ IsCP (ψ ∘ₗ φ)) ∧
    (∀ ψ ∈ dualCone P A B, ∀ φ ∈ coneOn P B C, φ ∘ₗ ψ ∈ dualCone P A C ∧ IsCP (φ ∘ₗ ψ)) := by sorry
end ChannelRandomization.PostProc
