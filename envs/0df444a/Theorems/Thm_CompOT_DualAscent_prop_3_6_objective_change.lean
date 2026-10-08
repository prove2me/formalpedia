-- Prove2me | Theorems.Thm_CompOT_DualAscent_prop_3_6_objective_change
-- name    : CompOT.DualAscent.prop_3_6_objective_change
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:39.359461+00:00
-- url     : https://prove2.me/theorems/5c1e3cf8-e129-4014-9256-d009018c1760
-- title:
--   §3.6, proof of Proposition 3.6, p. 417 — the step ε(1_S, −1_S′) changes ⟨f, a⟩ + ⟨g, b⟩ by ε(1_Sᵀa − 1_S′ᵀb)
-- statement:
--   Let $a \in \mathbb{R}^n$, $b \in \mathbb{R}^m$, potentials $f \in \mathbb{R}^n$, $g \in \mathbb{R}^m$, index sets $S \subset [\![n]\!]$, $S' \subset [\![m]\!]'$ and $\varepsilon \in \mathbb{R}$. Then
--   $$\big(\langle f + \varepsilon\mathbb{1}_S, a\rangle + \langle g - \varepsilon\mathbb{1}_{S'}, b\rangle\big) - \big(\langle f, a\rangle + \langle g, b\rangle\big) = \varepsilon\big(\mathbb{1}_S^{\mathsf T}a - \mathbb{1}_{S'}^{\mathsf T}b\big).$$
--
--   In the proof of Proposition 3.6 this is why it suffices to show $\mathbb{1}_S^{\mathsf T}a - \mathbb{1}_{S'}^{\mathsf T}b > 0$ to conclude that the step strictly improves the dual objective. It is an elementary stepping stone.
--
--   **Formalization Note** $\mathbb 1_S^{\mathsf T}a$ is written $\sum_{i\in S} a_i$. The page states only the consequence ("one still needs to prove that $\mathbb 1_S^{\mathsf T}a - \mathbb 1_{S'}^{\mathsf T}b > 0$ to ensure that $(\tilde f, \tilde g)$ has a better objective"); the identity is the computation behind it.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.6, proof of Proposition 3.6, pp. 416–417 (first line of p. 417)

import Mathlib
import Definitions.Def_CompOT_DualAscent_Defs

namespace CompOT.DualAscent

open Finset

/-- Proof of Proposition 3.6, p. 417, first line: moving `(f, g)` along `ε (𝟙_S, -𝟙_{S'})`
changes the objective `⟨f, a⟩ + ⟨g, b⟩` by `ε (𝟙_Sᵀ a - 𝟙_{S'}ᵀ b)`. -/
theorem prop_3_6_objective_change {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (f : Fin n → ℝ) (g : Fin m → ℝ) (S : Finset (Fin n)) (S' : Finset (Fin m)) (ε : ℝ) :
    CompOT.Duality.dualObj a b (f + ε • indicatorVec S) (g - ε • indicatorVec S') - CompOT.Duality.dualObj a b f g
      = ε * (∑ i ∈ S, a i - ∑ j ∈ S', b j) := by sorry

end CompOT.DualAscent
