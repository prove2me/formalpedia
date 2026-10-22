-- Prove2me | Theorems.Thm_ChannelRandomization_PostProc_lemma_4
-- name    : ChannelRandomization.PostProc.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:28.93997+00:00
-- url     : https://prove2.me/theorems/db89bd4d-b64f-4371-9ded-6c2d8fc6a35a
-- title:
--   Lemma 4, p. 11 — ‖β∘φ∘α‖_⋄ ≤ ‖φ‖_⋄ and ‖β∘φ∘α‖^⋄ ≤ ‖φ‖^⋄ for P- or CP-channels α, β
-- statement:
--   Let $\mathcal P$ be an admissible family and $\mathcal A',\mathcal A,\mathcal B,\mathcal B'$ C*-algebras. Let $\alpha:\mathcal A'\to\mathcal A$ and $\beta:\mathcal B\to\mathcal B'$ each be either a $\mathcal P$-channel (an element of $\mathcal C$) or a completely positive trace-preserving map in $\mathcal L$, and let $\phi\in\mathcal L(\mathcal A,\mathcal B)$. Then
--
--   $$\|\beta\circ\phi\circ\alpha\|_\diamond\le\|\phi\|_\diamond,\qquad \|\beta\circ\phi\circ\alpha\|^\diamond\le\|\phi\|^\diamond .$$
--
--   Both norms are therefore monotone under pre- and post-composition with channels. In Theorem 3 this bounds $\|\Gamma\circ\phi\|^\diamond\le\|\Gamma\|^\diamond$ when a decision rule $\phi$ is absorbed into a payoff map.
--
--   **Formalization Note.** "$\mathcal P$-channels or CP-channels" is read separately for each of $\alpha$ and $\beta$, which is the stronger of the two readings. CP-channels between the algebras are completely positive, trace-preserving maps in $\mathcal L(\cdot,\cdot)$.
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, p. 11, Lemma 4

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace ChannelRandomization.PostProc
theorem lemma_4 (P : AdmissibleFamily) {h' h k k' : ℕ} (A' : Fin h' → ℕ) (A : Fin h → ℕ)
    (B : Fin k → ℕ) (B' : Fin k' → ℕ)
    (α : Map h' h) (β : Map k k') (hα : α ∈ channels P A' A ∨ α ∈ cpChannels A' A)
    (hβ : β ∈ channels P B B' ∨ β ∈ cpChannels B B') (φ : Map h k) (hφ : InL A B φ) :
    diamond P A' B' (β ∘ₗ φ ∘ₗ α) ≤ diamond P A B φ ∧
      dualDiamond P A' B' (β ∘ₗ φ ∘ₗ α) ≤ dualDiamond P A B φ := by sorry
end ChannelRandomization.PostProc
