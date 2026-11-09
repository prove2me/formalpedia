-- Prove2me | Theorems.Thm_DirTeleMC_lemma_B_4
-- name    : DirTeleMC.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:32:26.169649+00:00
-- url     : https://prove2.me/theorems/d87f1ebf-463d-464f-b32b-d0f4e1ce33df
-- title:
--   Lemma B.4 — the increase is at most $(e-1)$ times the linear cost
-- statement:
--   **Lemma B.4.** Let $\Gamma > 0$ and $\Lambda \le \Gamma$, let $Q$ be a structure (or any load vector $L_Q$) with maximum load at most $\Lambda$, and let $L \le L'$ be states (coordinatewise). Then
--   1. $\Delta_L(Q) \le (e - 1)\, c_L(Q)$, and
--   2. $c_{L'}(Q) - c_L(Q) \le (\Lambda/\Gamma)\big(\Phi(L') - \Phi(L)\big)$.
--
--   Differences from the source:
--   - generalization: a structure Q with maximum load at most Λ → any load vector with every entry at most Λ; reason: the load vector of such a structure is one; both sides depend on Q only through its loads
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma B.4, p.27 (PDF p.28)

import Mathlib
import Definitions.Def_DirTeleMC_Phi

namespace DirTeleMC

/-- **Lemma B.4** (increase versus linear cost).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma B.4, p.27: "Let Q be a structure with maximum load at most Λ ≤ Γ, and let L ≤ L′ be states
(coordinatewise). Then (a) ∆_L(Q) ≤ (e − 1) c_L(Q), and (b) c_{L′}(Q) − c_L(Q) ≤ (Λ/Γ)(Φ(L′) − Φ(L))."

For a scale `Γ > 0`, a real `Λ ≤ Γ`, every load vector `L_Q` with all entries at most `Λ` (in particular the load
vector of a structure with maximum load at most `Λ`) and states `L ≤ L′`:
(a) `Δ_L(Q) ≤ (e − 1) c_L(Q)`, and (b) `c_{L′}(Q) − c_L(Q) ≤ (Λ/Γ)(Φ(L′) − Φ(L))`. -/
theorem lemma_B_4 {n : ℕ} (Γ Λ : ℝ) (hΓ : 0 < Γ) (hΛΓ : Λ ≤ Γ) (LQ : Fin n → ℕ)
    (hLQ : ∀ v, (LQ v : ℝ) ≤ Λ) (L L' : Fin n → ℕ) (hLL' : L ≤ L') :
    incr Γ L LQ ≤ (Real.exp 1 - 1) * lin Γ L LQ ∧
      lin Γ L' LQ - lin Γ L LQ ≤ (Λ / Γ) * (Phi Γ L' - Phi Γ L) := by sorry

end DirTeleMC
