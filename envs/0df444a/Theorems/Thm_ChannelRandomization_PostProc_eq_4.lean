-- Prove2me | Theorems.Thm_ChannelRandomization_PostProc_eq_4
-- name    : ChannelRandomization.PostProc.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:26.140526+00:00
-- url     : https://prove2.me/theorems/2a60aff7-b24c-41bd-a68b-eec287e97e3a
-- title:
--   Eq. (4), p. 9 — ‖φ‖_⋄ = sup_{σ∈𝔖(A)} sup_{−Φ_{I,σ} ≤* ξ ≤* Φ_{I,σ}} ⟨φ, ξ⟩
-- statement:
--   Let $\mathcal P$ be an admissible family, $\mathcal A\subseteq B(H)$, $\mathcal B\subseteq B(K)$ C*-algebras and $\phi\in\mathcal L(\mathcal A,\mathcal B)$. Then
--
--   $$\|\phi\|_\diamond=\sup_{\sigma\in\mathfrak S(\mathcal A)}\ \sup_{-\Phi_{I,\sigma}\le^*\xi\le^*\Phi_{I,\sigma}}\langle\phi,\xi\rangle ,$$
--
--   where $\xi$ ranges over $\mathcal L(\mathcal B,\mathcal A)$ and $\le^*$ is the order given by $\mathcal P^*(\mathcal B,\mathcal A)$. Here $\|\phi\|_\diamond$ is defined by formula (5), the norm whose unit ball is $\{x:\exists\alpha\in\mathcal C(\mathcal A,\mathcal B),\ -\alpha\le x\le\alpha\}$.
--
--   Formula (4) says that $\|\cdot\|_\diamond$ is the dual norm of $\|\cdot\|^\diamond$: the set of admissible $\xi$ is exactly the unit ball of $\|\cdot\|^\diamond$ on $\mathcal L(\mathcal B,\mathcal A)$. It is the identity $\max_{\Gamma\in\mathcal O^\diamond}\langle x,\Gamma\rangle=\|x\|_\diamond$ used to finish (iii)⇒(iv) in Theorem 3. For $\mathcal P=CP$ the norm $\|\cdot\|_\diamond$ is the usual diamond norm.
--
--   **Formalization Note.** The double supremum is a single `sSup` over the set of values $\langle\phi,\xi\rangle$ for $\sigma\in\mathfrak S(\mathcal A)$ and $\xi$ with $\xi+\Phi_{I,\sigma}$, $\Phi_{I,\sigma}-\xi\in\mathcal P^*(\mathcal B,\mathcal A)$; membership in $\mathcal P^*(\mathcal B,\mathcal A)$ forces $\xi\in\mathcal L(\mathcal B,\mathcal A)$.
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, p. 9, Eq. (4) = (5) (by Corollary 8 (i), p. 34, and Theorem 8, p. 33)

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace ChannelRandomization.PostProc
theorem eq_4 (P : AdmissibleFamily) {h k : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ)
    (φ : Map h k) (hφ : InL A B φ) :
    diamond P A B φ = sSup {r : ℝ | ∃ σ ∈ States A, ∃ ξ : Map k h,
      ξ + replacer σ ∈ dualCone P B A ∧ replacer σ - ξ ∈ dualCone P B A ∧ r = pair φ ξ} := by sorry
end ChannelRandomization.PostProc
