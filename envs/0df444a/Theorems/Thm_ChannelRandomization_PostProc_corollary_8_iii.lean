-- Prove2me | Theorems.Thm_ChannelRandomization_PostProc_corollary_8_iii
-- name    : ChannelRandomization.PostProc.corollary_8_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:42.268755+00:00
-- url     : https://prove2.me/theorems/90e26c6f-ea25-447d-a180-39835d486135
-- title:
--   Corollary 8 (iii), p. 34, instance used on p. 16: sup over O^⋄ ∩ P*(B,A) of ⟨c − c′, q⟩ = ½‖c − c′‖_⋄ for channels c, c′
-- statement:
--   Let $\mathcal P$ be an admissible family, $\mathcal A\subseteq B(H)$, $\mathcal B\subseteq B(K)$ C*-algebras, and $c,c'\in\mathcal C(\mathcal A,\mathcal B)$ two $\mathcal P$-channels. Let $\mathcal O^\diamond=\{q\in\mathcal L(\mathcal B,\mathcal A):\exists\sigma\in\mathfrak S(\mathcal A),\ -\Phi_{I,\sigma}\le^* q\le^*\Phi_{I,\sigma}\}$ be the unit ball of $\|\cdot\|^\diamond$. Then
--
--   $$\sup_{q\in\mathcal O^\diamond\cap\mathcal P^*(\mathcal B,\mathcal A)}\langle c-c',q\rangle=\tfrac12\,\|c-c'\|_\diamond .$$
--
--   This is Corollary 8 (iii) of the appendix — "if $b,b'\in B$, then $\sup_{q^*\in\mathcal O_{\tilde B}\cap Q^*}\langle b-b',q^*\rangle=\frac12\|b-b'\|_B$" — for the base section $B=\mathcal C(\mathcal A,\mathcal B)$ of $(\mathcal L(\mathcal A,\mathcal B),\mathcal P(\mathcal A,\mathcal B))$. It gives the bound $\langle\alpha\circ\Phi-\alpha'\circ\Psi,\Gamma\rangle\le\frac12\|\alpha\circ\Phi-\alpha'\circ\Psi\|_\diamond\|\Gamma\|^\diamond$ for positive payoff maps $\Gamma$, used in (iv)⇒(i) and in the last part of Theorem 3.
--
--   **Formalization Note.** $\mathcal O_{\tilde B}$ is written literally, as the set of $q$ with $q+\Phi_{I,\sigma}$ and $\Phi_{I,\sigma}-q$ in $\mathcal P^*(\mathcal B,\mathcal A)$ for some state $\sigma$ of $\mathcal A$; the supremum is `sSup` of a real set.
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, p. 34, Corollary 8 (iii), in the instance used on p. 16 (proof of Theorem 3, (iv)⇒(i) and the Moreover clause)

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace ChannelRandomization.PostProc
theorem corollary_8_iii (P : AdmissibleFamily) {h k : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ)
    (c c' : Map h k) (hc : c ∈ channels P A B) (hc' : c' ∈ channels P A B) :
    sSup {r : ℝ | ∃ q ∈ dualCone P B A, (∃ σ ∈ States A,
        q + replacer σ ∈ dualCone P B A ∧ replacer σ - q ∈ dualCone P B A) ∧
        r = pair (c - c') q} =
      1 / 2 * diamond P A B (c - c') := by sorry
end ChannelRandomization.PostProc
