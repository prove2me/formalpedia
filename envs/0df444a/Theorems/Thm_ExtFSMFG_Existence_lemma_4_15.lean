-- Prove2me | Theorems.Thm_ExtFSMFG_Existence_lemma_4_15
-- name    : ExtFSMFG.Existence.lemma_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:37.510988+00:00
-- url     : https://prove2.me/theorems/ec2a057b-fb50-41b5-b6eb-d49264984a8c
-- title:
--   Lemma 4.15, p. 23 — ∫₀ᵀ W₁(ν⁽ⁿ⁾_t, ν⁽⁰⁾_t) dt → 0 implies L(dt) × δ_{ν⁽ⁿ⁾_t} → L(dt) × δ_{ν⁽⁰⁾_t} stably
-- statement:
--   Let $T>0$ and $A\subseteq\mathbb R^l$ compact. Let $\nu^{(n)}$, $n\ge0$, be measurable maps $[0,T]\to\mathcal P(A)$ with
--   $$\int_0^T\mathcal W_1\big(\nu^{(n)}_t,\nu^{(0)}_t\big)\,dt\longrightarrow0 .$$
--   Then $\mathcal L(dt)\times\delta_{\nu^{(n)}_t}(d\nu)\to\mathcal L(dt)\times\delta_{\nu^{(0)}_t}(d\nu)$ in $\mathcal R_0$ for the stable topology.
--
--   This lemma reduces the continuity of the control component $\Phi^\eta$ of the fixed-point map to an $L^1$ estimate in $\mathcal W_1$.
--
--   **Formalization Note** The elements of $\mathcal R$ are given with their underlying measures equal to $\mathcal L(dt)\times\delta_{\nu_t}(d\nu)$; convergence is in $\mathcal R$, which is the same as in the subspace $\mathcal R_0$ for points of $\mathcal R_0$.
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, p. 23, Lemma 4.15

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model
import Definitions.Def_ExtFSMFG_Existence_BSDE
import Definitions.Def_ExtFSMFG_Existence_FixedPoint

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

theorem lemma_4_15 {m l : ℕ} {T : ℝ≥0} (hT : 0 < T)
    (A : Set (EuclideanSpace ℝ (Fin l))) (hA : IsCompact A)
    (νs : ℕ → ℝ≥0 → PA A) (ν₀ : ℝ≥0 → PA A)
    (hνs : ∀ n, Measurable fun t : Set.Icc (0 : ℝ≥0) T => νs n t)
    (hν₀ : Measurable fun t : Set.Icc (0 : ℝ≥0) T => ν₀ t)
    (hW : Tendsto (fun n => ∫ t in Set.Icc (0 : ℝ) T, W1 (νs n t.toNNReal) (ν₀ t.toNNReal))
      atTop (𝓝 0))
    (η : ℕ → Rstable T A) (η₀ : Rstable T A)
    (hη : ∀ n, (η n).toMeasure = LdeltaFlow (νs n)) (hη₀ : η₀.toMeasure = LdeltaFlow ν₀) :
    Tendsto η atTop (𝓝 η₀) := by sorry

end ExtFSMFG.Existence
