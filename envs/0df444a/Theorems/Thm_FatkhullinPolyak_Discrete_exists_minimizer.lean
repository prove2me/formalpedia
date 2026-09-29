-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_exists_minimizer
-- name    : FatkhullinPolyak.Discrete.exists_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:38:07.577434+00:00
-- url     : https://prove2.me/theorems/0bca0064-19a9-43ce-b804-58a26b1ca23c
-- title:
--   Corollary 3.10 — existence of an optimal gain $K_*\in\mathcal S$
-- statement:
--   Under the standing assumptions ($Q,R,\Sigma\succ0$, $\operatorname{rank}C=r$, $B\ne0$, and a stabilizing gain $K_0\in\mathcal S$ exists), the LQR cost attains its minimum on $\mathcal S$: there is $K_*\in\mathcal S$ with
--   $$f(K_*)\le f(K)\qquad\text{for all }K\in\mathcal S .$$
--
--   The optimal gain $K_*$ is the target of the linear-rate statement for state feedback (Theorem 4.2) and appears in the LPL constant (3.11).
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 7, Corollary 3.10

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Corollary 3.10 (p. 7): there exists a minimum point `K⋆ ∈ S` of `f` on `S`
(under the standing assumptions of p. 3, including the existence of `K₀ ∈ S`). -/
theorem exists_minimizer {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (hK₀ : K₀ ∈ stabSet A B C) :
    ∃ Kstar ∈ stabSet A B C, ∀ K ∈ stabSet A B C,
      lqrCost A B C Q R Sig Kstar ≤ lqrCost A B C Q R Sig K := by sorry

end FatkhullinPolyak.Discrete
