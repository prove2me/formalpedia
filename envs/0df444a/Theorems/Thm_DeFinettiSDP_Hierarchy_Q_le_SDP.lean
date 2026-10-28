-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_Q_le_SDP
-- name    : DeFinettiSDP.Hierarchy.Q_le_SDP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:38.870465+00:00
-- url     : https://prove2.me/theorems/a1e3d8c0-9b06-4b2a-ac11-78670bdbb6d8
-- title:
--   Proof of Theorem 3.1, p. 11 — 0 ≤ SDPₙ − Q: every level of the hierarchy is an outer bound
-- statement:
--   For every level $N\ge1$ of the hierarchy,
--
--   $$Q\ \le\ \mathrm{SDP}_N,$$
--
--   where $Q$ is the optimal value of the constrained bilinear program (2) and $\mathrm{SDP}_N$ the optimal value of the semidefinite program of Theorem 3.1 with $N$ copies of $B$.
--
--   Every level is a relaxation of $Q$: the lower half of Theorem 3.1.
--
--   **Formalization Note** `SDPval … n` is the page's $\mathrm{SDP}_{n+1}$, so the statement is for every $n\in\mathbb N$ with $n+1$ copies of $B$. Both values are suprema of real sets (see the definition file).
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, proof of Theorem 3.1, p. 11, first sentence

import Mathlib
import Definitions.Def_DeFinettiSDP_Hierarchy_Problem
open Matrix

namespace DeFinettiSDP.Hierarchy

/-- **0 ≤ SDP_n − Q** (arXiv:1810.12197v3, proof of Theorem 3.1, p. 11, first sentence): every
level of the hierarchy is an outer bound, `Q ≤ SDP_{n+1}` for every `n` (`SDPval … n` is the
level with `n + 1` copies of `B`). -/
theorem Q_le_SDP {dA dB cA cB : ℕ} (G : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ) :
    ∀ n : ℕ, Qval G Λ Γ X Y ≤ SDPval G Λ Γ X Y n := by sorry

end DeFinettiSDP.Hierarchy
