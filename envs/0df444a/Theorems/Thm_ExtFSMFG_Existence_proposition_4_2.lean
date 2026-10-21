-- Prove2me | Theorems.Thm_ExtFSMFG_Existence_proposition_4_2
-- name    : ExtFSMFG.Existence.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:12.34647+00:00
-- url     : https://prove2.me/theorems/c4da0caf-3d0d-4545-b15a-ed24b23d56a7
-- title:
--   Proposition 4.2, p. 13 — 𝒫₀ is convex and relatively compact in 𝒫
-- statement:
--   Let $T>0$ and let $\mathbb P$ be the reference measure on $D=\Omega$. For every constant $C_0$, the set
--   $$\mathcal P_0=\Big\{\mathbb Q\in\mathcal P:\ \frac{d\mathbb Q}{d\mathbb P}=L,\ \mathbb E^{\mathbb P}[L^2]\le C_0\Big\}$$
--   is convex (for $\mathbb Q_1,\mathbb Q_2\in\mathcal P_0$ and $\theta\in[0,1]$, $\theta\mathbb Q_1+(1-\theta)\mathbb Q_2\in\mathcal P_0$) and relatively compact in $\mathcal P$ for the weak topology induced by the J1 topology on $D$: its closure is compact.
--
--   This provides the compact convex set of state mean fields on which Schauder's theorem is applied.
--
--   **Formalization Note** The paper fixes $C_0$ later (Proposition 4.10); the proof works for every $C_0$, and for $C_0<1$ the set is empty. Convexity is stated as closure under convex combinations of measures, since $\mathcal P$ is not a vector space.
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, p. 13, Proposition 4.2, (33)–(35)

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model
import Definitions.Def_ExtFSMFG_Existence_BSDE
import Definitions.Def_ExtFSMFG_Existence_FixedPoint

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

theorem proposition_4_2 {m : ℕ} {T : ℝ≥0} (hT : 0 < T)
    (p₀ : stdSimplex ℝ (Fin m)) (P : Measure (Omega m T)) [IsProbabilityMeasure P]
    (hP : IsReference T p₀ P) (C₀ : ℝ) :
    (∀ Q₁ ∈ P0set P C₀, ∀ Q₂ ∈ P0set P C₀, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      ∃ Q ∈ P0set P C₀,
        Q.toMeasure = ENNReal.ofReal θ • Q₁.toMeasure + ENNReal.ofReal (1 - θ) • Q₂.toMeasure) ∧
      IsCompact (closure (P0set P C₀)) := by sorry

end ExtFSMFG.Existence
