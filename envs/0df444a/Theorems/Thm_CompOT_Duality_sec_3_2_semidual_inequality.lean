-- Prove2me | Theorems.Thm_CompOT_Duality_sec_3_2_semidual_inequality
-- name    : CompOT.Duality.sec_3_2_semidual_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:42.425196+00:00
-- url     : https://prove2.me/theorems/23368725-4c88-487e-905f-b402099a2507
-- title:
--   §3.2, p. 403 — for (f, g) ∈ R(C): ⟨f, a⟩ + ⟨g, b⟩ ≤ ⟨f, a⟩ + ⟨f^C, b⟩
-- statement:
--   Let $a \in \Sigma_n$, $b \in \Sigma_m$ be histograms, $C \in \mathbb R^{n\times m}$, and $(f,g) \in \mathbf R(C)$. With $f^C$ the $C$-transform of $f$,
--   $$\langle f,a\rangle + \langle g,b\rangle \;\le\; \langle f,a\rangle + \langle f^C,b\rangle.$$
--
--   Replacing $g$ by $f^C$ never decreases the dual objective, so the dual problem (2.20) can be reduced to a maximization over $f$ alone.
--
--   **Formalization Note** $a \in \Sigma_n$ forces $n \ge 1$, so $f^C$ is a genuine minimum. Only $b \ge 0$ is needed for the inequality; the full histogram hypotheses are the book's standing convention.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.2, p. 403, display preceding (3.5)

import Mathlib
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.Duality

/-- §3.2, p. 403: for histograms `a ∈ Σ_n`, `b ∈ Σ_m` and any dual feasible `(f, g) ∈ R(C)`,
`⟨f, a⟩ + ⟨g, b⟩ ≤ ⟨f, a⟩ + ⟨f^C, b⟩`. -/
theorem sec_3_2_semidual_inequality {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hfg : dualFeasible C f g) :
    dualObj a b f g ≤ dualObj a b f (cTransform C f) := by sorry

end CompOT.Duality
