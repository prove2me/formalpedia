-- Prove2me | Theorems.Thm_ChannelRandomization_PostProc_corollary_8_ii
-- name    : ChannelRandomization.PostProc.corollary_8_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:32.459332+00:00
-- url     : https://prove2.me/theorems/632fc0b8-f655-478e-b1b8-e0ea73321bdf
-- title:
--   Corollary 8 (ii), p. 34, instance for ‖·‖^⋄ (as used on p. 15): ‖x‖^⋄ = sup_{φ∈𝒞(A,B)} ⟨φ, x⟩ for x ∈ P*(B,A)
-- statement:
--   Let $\mathcal P$ be an admissible family and $\mathcal A\subseteq B(H)$, $\mathcal B\subseteq B(K)$ C*-algebras. For every $x\in\mathcal P^*(\mathcal B,\mathcal A)$,
--
--   $$\|x\|^\diamond=\sup_{\phi\in\mathcal C(\mathcal A,\mathcal B)}\langle\phi,x\rangle .$$
--
--   This is Corollary 8 (ii) of the appendix — "if $x\in Q$, then $\|x\|_B=\sup_{\tilde b\in\tilde B}\langle x,\tilde b\rangle$" — in the ordered space $(\mathcal L(\mathcal B,\mathcal A),\mathcal P^*(\mathcal B,\mathcal A))$ with base section $\mathcal S(\mathcal B,\mathcal A)=\{\Phi_{I,\sigma}:\sigma\in\mathfrak S(\mathcal A)\}$ (Lemma 2), whose norm is $\|\cdot\|^\diamond$ and whose dual section is $\mathcal C(\mathcal A,\mathcal B)$. On positive elements the dual-diamond norm is thus a plain supremum of payoffs over channels; this is the step (i)⇒(ii) of Theorem 3.
--
--   **Formalization Note.** $\|\cdot\|^\diamond$ is defined by formula (7) as an infimum; the supremum is `sSup` of a real set, which is nonempty and bounded above when the dimensions are positive (in dimension 0 both sides are 0).
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, p. 34, Corollary 8 (ii), in the instance used on p. 15 (proof of Theorem 3, (i)⇒(ii))

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace ChannelRandomization.PostProc
theorem corollary_8_ii (P : AdmissibleFamily) {h k : ℕ} (A : Fin h → ℕ) (B : Fin k → ℕ)
    (x : Map k h) (hx : x ∈ dualCone P B A) :
    dualDiamond P B A x = sSup {r : ℝ | ∃ φ ∈ channels P A B, r = pair φ x} := by sorry
end ChannelRandomization.PostProc
