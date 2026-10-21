-- Prove2me | Theorems.Thm_CoProdBundle_Equil_proof_i_prefix
-- name    : CoProdBundle.Equil.proof_i_prefix
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:40.922038+00:00
-- url     : https://prove2.me/theorems/70b9b462-feb1-44cb-8d74-f2b00eb12a7c
-- title:
--   Proof of Lemma 1, step (i), p. 30 — with ascending costs the active producers of an equilibrium are 1, …, K
-- statement:
--   Under the standing assumptions ($I \ge 1$ producers with costs $0 < c_1 \le \dots \le c_I$, $b > 0$, $A - bw > 0$, $0 < \theta < 2/3$, $0 < \gamma < 1$), let $(Q_1,\dots,Q_I)$ be a Nash equilibrium with positive aggregate output. If producer $j$ is active ($Q_j > 0$) and $i \le j$, then producer $i$ is active:
--   $$i \le j,\ Q_j > 0 \implies Q_i > 0.$$
--
--   So the active producers form an initial segment $\{1,\dots,m\}$ of the cost order, and the individual-rationality constraints reduce to the one of the last active producer.
--
--   **Formalization Note** Lean's producers are `Fin I` with the order of their indices; the paper's ascending cost order is the hypothesis `Monotone c`.
-- source:
--   Bhargava, Bundling for Flexibility and Variety: An Economic Model for Multiproducer Value Aggregation, author's accepted manuscript (2020; Manag. Sci. doi:10.1287/mnsc.2020.3662), Appendix A.1, proof of Lemma 1, step (i), p. 30

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

namespace CoProdBundle.Equil

/-- Proof of Lemma 1, step (i), p. 30: with ascending costs, the active producers of an
equilibrium form an initial segment. -/
theorem proof_i_prefix (I : ℕ) (hI : 0 < I) (c : Fin I → ℝ) (hc0 : ∀ i, 0 < c i)
    (hcm : Monotone c) (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (q : Fin I → ℝ) (hq : IsNashEq γ A b w θ c q) (hQ : 0 < total q) :
    ∀ i j : Fin I, i ≤ j → 0 < q j → 0 < q i := by sorry

end CoProdBundle.Equil
