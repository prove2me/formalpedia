-- Prove2me | Theorems.Thm_AsymSpecConn_lemma_2_9
-- name    : AsymSpecConn.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:40:37.193722+00:00
-- url     : https://prove2.me/theorems/4cca299b-44ef-4c67-bbf9-8b4f21c27431
-- title:
--   Lemma 2.9 — the cover property makes $w_\theta$ $\mathcal A$-good
-- statement:
--   Let $\mathcal S$ be a Strassen semiring and let $\mathcal A\subseteq\mathcal S\setminus\{0\}$ be multiplicatively closed and contain every positive integer. If $g_1,\dots,g_r\in\Delta$ have the $\mathcal A$-cover property, then for every probability vector $\theta$ on $[r]$ the geometric average $w_\theta=\prod_i g_i^{\theta_i}$ is $\mathcal A$-good.
--
--   This is the step that turns the cover property into new spectral points through the construction $F_w$.
--
--   Differences from the source:
--
--   - encoding: w_θ as an A-good function on A → IsAGood applied to geomAvg g θ : S → ℝ≥0; reason: the source applies its definition through restriction to A (p.14)
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 2.9, p.17

import Mathlib
import Definitions.Def_AsymSpecConn_IsStrassenSemiring
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_IsAGood
import Definitions.Def_AsymSpecConn_geomAvg
import Definitions.Def_AsymSpecConn_HasACoverProperty

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **Lemma 2.9** (p.17 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Let A ⊆ S \ {0} be multiplicatively
closed and contain every positive integer. If g1, …, gr ∈ ∆ have the A-cover property, then for
every θ ∈ P([r]), the function wθ is A-good."

**Formalization Note** `P([r])` is `stdSimplex ℝ (Fin r)`; `w_θ` is `geomAvg g θ`. `S` is a
Strassen semiring (standing assumption of §2, p.12). -/
theorem lemma_2_9 {S : Type*} [CommSemiring S] (P : Preorder S) (hS : IsStrassenSemiring S P)
    (A : Set S) (hA0 : ∀ a ∈ A, a ≠ 0) (hAmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A)
    (hAnat : ∀ m : ℕ, 1 ≤ m → (m : S) ∈ A) {r : ℕ} (g : Fin r → ↥(Spectrum S P))
    (hg : HasACoverProperty P A g) (θ : Fin r → ℝ) (hθ : θ ∈ stdSimplex ℝ (Fin r)) :
    IsAGood P A (geomAvg g θ) := by sorry

end AsymSpecConn
