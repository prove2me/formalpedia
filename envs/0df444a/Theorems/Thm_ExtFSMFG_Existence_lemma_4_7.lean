-- Prove2me | Theorems.Thm_ExtFSMFG_Existence_lemma_4_7
-- name    : ExtFSMFG.Existence.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:20.583616+00:00
-- url     : https://prove2.me/theorems/39b754fe-ae0b-434f-a1bd-dfcd8c6a6657
-- title:
--   Lemma 4.7, p. 16 — ℛ₀ is a convex and compact subset of ℛ for the stable topology
-- statement:
--   Let $T>0$ and $A\subseteq\mathbb R^l$ compact. The set $\mathcal R_0$ of probability measures on $[0,T]\times\mathcal P(A)$ whose marginal on $[0,T]$ is the normalized Lebesgue measure $\mathcal L(dt)=\frac1Tdt$ is convex (closed under convex combinations $\theta\eta_1+(1-\theta)\eta_2$, $\theta\in[0,1]$) and compact in $\mathcal R$ for the stable topology of Definition 4.4.
--
--   This provides the compact convex set of randomized control mean fields on which Schauder's theorem is applied.
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, p. 16, Lemma 4.7

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model
import Definitions.Def_ExtFSMFG_Existence_BSDE
import Definitions.Def_ExtFSMFG_Existence_FixedPoint

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

theorem lemma_4_7 {m l : ℕ} {T : ℝ≥0} (hT : 0 < T)
    (A : Set (EuclideanSpace ℝ (Fin l))) (hA : IsCompact A) :
    (∀ η₁ ∈ R0set T A, ∀ η₂ ∈ R0set T A, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∃ η ∈ R0set T A,
        η.toMeasure = ENNReal.ofReal θ • η₁.toMeasure + ENNReal.ofReal (1 - θ) • η₂.toMeasure) ∧
      IsCompact (R0set T A) := by sorry

end ExtFSMFG.Existence
