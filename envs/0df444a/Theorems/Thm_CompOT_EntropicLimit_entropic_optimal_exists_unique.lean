-- Prove2me | Theorems.Thm_CompOT_EntropicLimit_entropic_optimal_exists_unique
-- name    : CompOT.EntropicLimit.entropic_optimal_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:55.122537+00:00
-- url     : https://prove2.me/theorems/a9c4634e-8742-4cc5-a85a-a1dd1163d747
-- title:
--   §4.1, p. 425 — for ε > 0 the entropic problem (4.2) has a unique optimal solution P_ε
-- statement:
--   Let $a \in \Sigma_n$ and $b \in \Sigma_m$ be histograms (nonnegative entries summing to $1$), let $C \in \mathbb R^{n\times m}$ be a cost matrix and let $\varepsilon > 0$. Then the entropically regularized transport problem
--   $$L^\varepsilon_C(a,b) = \min_{P \in U(a,b)} \langle P, C\rangle - \varepsilon \mathbf H(P)$$
--   has exactly one minimizer $P_\varepsilon \in U(a,b)$.
--
--   This is what makes "the solution $P_\varepsilon$ of (4.2)" well defined, and it guarantees that the hypotheses of Proposition 4.1 can be met.
--
--   **Formalization Note** $\mathbf H$ uses $0\log 0 = 0$; indices are 0-based.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §4.1, sentence after (4.2), p. 425

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs

namespace CompOT.EntropicLimit

/-- §4.1, p. 425: for `ε > 0` and histograms `a ∈ Σ_n`, `b ∈ Σ_m`, problem (4.2) has a
unique optimal solution `P_ε`. -/
theorem entropic_optimal_exists_unique {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (ε : ℝ) (hε : 0 < ε) :
    ∃! P : Matrix (Fin n) (Fin m) ℝ, IsEntropicOptimal C a b ε P := by sorry

end CompOT.EntropicLimit
