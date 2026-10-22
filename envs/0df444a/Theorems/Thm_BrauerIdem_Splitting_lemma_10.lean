-- Prove2me | Theorems.Thm_BrauerIdem_Splitting_lemma_10
-- name    : BrauerIdem.Splitting.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:23.97443+00:00
-- url     : https://prove2.me/theorems/e2265505-da5d-46af-88b3-ad0874eaa46c
-- title:
--   Lemma 10, p. 7 — 0 → J → Λ → Λ/J → 0 splits iff some φ has φ ≡ 1 mod J and φJ = Jφ = 0; φ is then a unique central idempotent
-- statement:
--   Let $\Lambda$ be a unital ring and $J$ a two-sided ideal. The short exact sequence of $\Lambda$-bimodules
--
--   $$
--   0\longrightarrow J\longrightarrow\Lambda\longrightarrow\Lambda/J\longrightarrow0
--   $$
--
--   splits if and only if there is $\varphi\in\Lambda$ with $\varphi-1\in J$ and $\varphi j=j\varphi=0$ for every $j\in J$. Such a $\varphi$ is unique, idempotent, and central.
--
--   This criterion identifies the algebraic property required of the element constructed in Theorem 14.
--
--   **Formalization Note** A splitting is an additive section of the quotient map satisfying both left and right $\Lambda$-linearity. The Lean statement uses an arbitrary unital ring, as in the chapter brief's general ring formulation.
-- source:
--   King, Martin, Parker, On central idempotents in the Brauer algebra, arXiv:1609.01183v1, p. 7, Lemma 10

import Mathlib

namespace BrauerIdem.Splitting

/-- King–Martin–Parker, Lemma 10, p. 7. -/
theorem lemma_10 {Λ : Type*} [Ring Λ] (J : TwoSidedIdeal Λ) :
    (∃ s : J.ringCon.Quotient →+ Λ,
      (∀ x, J.ringCon.mk' (s x) = x) ∧
      (∀ (a b : Λ) (x : J.ringCon.Quotient),
        s (J.ringCon.mk' a * x * J.ringCon.mk' b) = a * s x * b)) ↔
    (∃ φ : Λ, φ - 1 ∈ J ∧
      (∀ j ∈ J, φ * j = 0 ∧ j * φ = 0) ∧
      (∀ ψ : Λ, ψ - 1 ∈ J → (∀ j ∈ J, ψ * j = 0 ∧ j * ψ = 0) → ψ = φ) ∧
      φ * φ = φ ∧ (∀ a : Λ, φ * a = a * φ)) := by sorry

end BrauerIdem.Splitting
