-- Prove2me | Theorems.Thm_ComplementsRev_Approx_corollary_3_1
-- name    : ComplementsRev.Approx.corollary_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:53.287334+00:00
-- url     : https://prove2.me/theorems/1ade112f-6bef-466e-83dc-6dd125bfda28
-- title:
--   Corollary 3.1 — duality benchmark for revenue
-- statement:
--   Let $D$ be the finite product hyperedge population defined in §2, and let a truthful, individually rational lottery mechanism earn expected revenue $\operatorname{Rev}(m)$. Fix a tie rank for the favorite nonempty hyperedge. Then
--
--   $$\operatorname{Rev}(m)\le \operatorname{NON\text{-}FAVORITE}(D)+\operatorname{SINGLE}(D).$$
--
--   NON-FAVORITE counts value from hyperedges outside their favorite regions, while SINGLE counts the positive ironed virtual value of the favorite hyperedge. This is the paper's benchmark that separates the two revenue estimates.
--
--   **Formalization Note** The inequality is stated for each truthful mechanism rather than through a real supremum over mechanisms. The benchmarks are expectations over the generating hypergraph $w$, as the paper's integrands read $w$; on the support, $w$ is recovered from $v$ (weights vanish off $C$, and $v(S)=\sum_{U\subseteq S}w(U)$ for $S\in C$), so this is the paper's $\mathbb E_{v\leftarrow D}$.
-- source:
--   Eden, Feldman, Friedler, Talgam-Cohen & Weinberg, A Simple and Approximately Optimal Mechanism for a Buyer with Complements, arXiv:1612.04746v2, Corollary 3.1, p. 6

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

namespace ComplementsRev.Approx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Eden et al., Corollary 3.1, p. 6: the duality benchmark. -/
theorem corollary_3_1 (P : Population ι) (rk : Finset ι → ℕ)
    (hrk : Function.Injective rk) (m : Mech ι) (hm : IsTruthful P m) :
    revenue P m ≤ NONFAV P rk + SINGLE P rk := by sorry

end ComplementsRev.Approx
