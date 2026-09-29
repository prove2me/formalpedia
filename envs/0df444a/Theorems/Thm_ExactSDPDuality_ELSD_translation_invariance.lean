-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_translation_invariance
-- name    : ExactSDPDuality.ELSD.translation_invariance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:16:01.869038+00:00
-- url     : https://prove2.me/theorems/d73d6c1c-9bde-4d95-84f6-9260824fbea9
-- title:
--   §2.5 — 𝒞ₖ, 𝒰ₖ, 𝒲ₖ are unchanged when Q₀ is replaced by Q(x̄), x̄ ∈ G
-- statement:
--   Let $Q_0,\dots,Q_m$ be real symmetric $n\times n$ matrices and $\bar x\in G = \{x\mid Q(x)\succeq 0\}$. Translating the primal by $\bar x$ replaces $Q_0$ by $Q(\bar x) = Q_0 - \sum_i\bar x_iQ_i$ and leaves $Q_1,\dots,Q_m$ unchanged. For every $k$, the sets
--   $$\mathcal C_k,\qquad \mathcal U_k,\qquad \mathcal W_k$$
--   built from the data $(Q(\bar x), Q_1,\dots,Q_m)$ coincide with those built from $(Q_0, Q_1,\dots,Q_m)$.
--
--   This is the reduction that lets the proof of the Duality Theorem assume that the origin is primal feasible.
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 150, §2.5, last paragraph

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Translation invariance (Ramana 1997, §2.5, p. 150): for `x̄ ∈ G`, the sets `𝒞ₖ`, `𝒰ₖ` and
`𝒲ₖ` built from the data `(Q(x̄), Q₁, …, Qₘ)` coincide with those built from
`(Q₀, Q₁, …, Qₘ)`, for every `k`. -/
theorem translation_invariance {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (xbar : Fin m → ℝ) (hx : xbar ∈ feasibleSet Q0 Q) (k : ℕ) :
    (∀ U W : ℕ → Matrix (Fin n) (Fin n) ℝ,
        IsCSeq (Qaff Q0 Q xbar) Q k U W ↔ IsCSeq Q0 Q k U W) ∧
      Uset (Qaff Q0 Q xbar) Q k = Uset Q0 Q k ∧
      Wset (Qaff Q0 Q xbar) Q k = Wset Q0 Q k := by sorry

end ExactSDPDuality.ELSD
