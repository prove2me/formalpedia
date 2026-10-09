-- Prove2me | Theorems.Thm_ExpanderBIS_Potts_theorem_3_reduction
-- name    : ExpanderBIS.Potts.theorem_3_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:34:49.657178+00:00
-- url     : https://prove2.me/theorems/40c8a641-32cf-4ef5-bd0d-8df9a88f08c7
-- title:
--   Theorem 3 core — Potts reduction and Kotecký–Preiss condition
-- statement:
--   Let $G$ be a nonempty finite $\alpha$-expander of maximum degree at most $\Delta$. Suppose $\alpha>0$, $\Delta\ge3$, $q\ge2$, and $\beta\ge(4+2\log(q\Delta))/\alpha$. With $n=|V(G)|$, $e(G)=|E(G)|$, and $\Xi(G)$ the Potts polymer partition sum, define $\widehat Z=q e^{\beta e(G)}\Xi(G)$. Then
--
--   $$
--   e^{-2e^{-n}}\widehat Z\le Z_{G,q}(\beta)\le e^{2e^{-n}}\widehat Z.
--   $$
--
--   Moreover, every polymer $\gamma$ satisfies the Kotecký–Preiss condition with $g(\gamma)=|\gamma|$:
--
--   $$
--   \sum_{\gamma':\,d(\gamma',\gamma)\le1}
--     w_{\gamma'}e^{2|\gamma'|}\le|\gamma|.
--   $$
--
--   Together these statements provide the deterministic approximation and convergence condition used by the paper's algorithmic Theorem 3.
--
--   **Formalization Note** The vertex set is nonempty because the reduction fails on the empty graph. The factor $2e^{-n}$ is the composed error of Lemmas 12 and 13, rather than a separately printed bound. The sum includes $\gamma$ itself and every overlapping or adjacent polymer. The FPTAS and sampling running times are outside this Lean statement.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, pp. 4, 15–16, Theorem 3 and §3.2–3.3

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting

namespace ExpanderBIS.Potts

open Finset

/-- Deterministic reduction and Kotecký–Preiss condition used for Theorem 3,
    §3.3, p. 16. -/
theorem theorem_3_reduction {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α β : ℝ) (Δ q : ℕ)
    (hα : 0 < α) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q)
    (hdeg : ∀ v, G.degree v ≤ Δ) (hG : IsExpander G α)
    (hβ : (4 + 2 * Real.log ((q * Δ : ℕ) : ℝ)) / α ≤ β) :
    IsRelApprox (2 * Real.exp (-(Fintype.card V : ℝ)))
      ((q : ℝ) * Real.exp (β * (#G.edgeFinset : ℝ)) * polymerXi G q β)
      (pottsZ G q β) ∧
    ∀ γ ∈ polymers G,
      (∑ γ' ∈ incompatiblePolymers G γ,
        weight G q β γ' * Real.exp (2 * (#γ' : ℝ))) ≤ (#γ : ℝ) := by sorry

end ExpanderBIS.Potts
