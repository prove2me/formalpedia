-- Prove2me | Theorems.Thm_EngageInfo_eq_8_concavification
-- name    : EngageInfo.eq_8_concavification
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:20.788266+00:00
-- url     : https://prove2.me/theorems/f84ab1fe-d159-4cc9-9f58-05f983978a81
-- title:
--   (8) — the seller's optimal value is the concave closure $V^*(\alpha^0)$, the least concave majorant of $v^*$
-- statement:
--   Assume $\alpha_1<\alpha_{\bar e}$ and let $V^*$ be the concave closure of $v^*$. Then:
--
--   1. for every prior $\alpha^0\in(0,1)$, the largest value of $W(\pi)$ over feasible designs exists and equals $V^*(\alpha^0)$;
--   2. $V^*$ is concave on $[0,1]$ and $V^*\ge v^*$ there;
--   3. $V^*\le g$ on $[0,1]$ for every function $g$ that is concave on $[0,1]$ with $g\ge v^*$ there.
--
--   That is, an optimal design exists, the seller's optimal value is $V^*(\alpha^0)$, and $V^*$ is the smallest concave function weakly above $v^*$.
--
--   Differences from the source:
--   - encoding: "V∗(α) is the smallest concave function that is weakly greater than v∗(α)"; "the seller's expected value under the optimal information structure is given by V∗(α⁰)" → V∗ concave on [0,1], V∗ ≥ v∗ there, V∗ ≤ every concave majorant there; for α⁰ ∈ (0,1), V∗(α⁰) is the greatest value W(π) of a feasible design; reason: beliefs range over [0,1] and the prior over (0,1) (p.6); "given by" is read as the value being attained
--   - encoding: co(v∗), the convex hull of the graph {(α, x) | x = v∗(α), α ∈ [0,1]}, and sup → convexHull ℝ of that graph in ℝ × ℝ, and the real sSup of the fibre; reason: Mathlib convention; the fibre is nonempty and bounded above for α ∈ [0,1], so sSup is the supremum
--   - reading: "the seller's equilibrium expected payoff" v∗(α), with "the equilibrium" called unique (p.8) → v∗(α) = the maximum of the seller's payoffs over all pure subgame-perfect equilibria at belief α (seller-preferred equilibrium); reason: at α ∈ {α₀, α₁, α_ē} the subgame has several SPE with different seller payoffs; the closed interval of Lemma 1 and the values of (6) there are those of the seller-preferred SPE
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, §3.2, (8), p.12

import Mathlib
import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_vstar
import Definitions.Def_EngageInfo_designs
import Definitions.Def_EngageInfo_designValue
import Definitions.Def_EngageInfo_concaveClosure

namespace EngageInfo

/-- **Concavification (8): the optimal value is the concave closure V*(α⁰).**
Guo, *Designing Information to Engage Customers*, Management Science (2025), §3.2, p.12, (8): "we
follow Kamenica and Gentzkow to define the concave closure of v∗ as V∗(α) ≡ sup{x|(α, x) ∈ co(v∗)}
… Thus, as explained by Kamenica and Gentzkow (2011), V∗(α) is the smallest concave function that
is weakly greater than v∗(α) … It follows that the seller's expected value under the optimal
information structure is given by V∗(α⁰)."

Assume `α₁ < α_ē`. Then
1. for every prior `α⁰ ∈ (0, 1)`, `V*(α⁰)` is the greatest value `W(π)` of a feasible design (so
   optimal designs exist and earn exactly `V*(α⁰)`);
2. `V*` is concave on `[0, 1]` and `V* ≥ v*` there;
3. `V* ≤ g` on `[0, 1]` for every `g` concave on `[0, 1]` with `g ≥ v*` there.

**Formalization Note** `V* = concaveClosure (vstar M)`, the supremum of the fibre of
`convexHull ℝ` of the graph of `v*` over `[0, 1]`. -/
theorem eq_8_concavification (M : Params) (hα : M.α₁ < M.αbar) :
    (∀ a0 ∈ Set.Ioo (0 : ℝ) 1,
      IsGreatest (designValue M a0 '' designs) (concaveClosure (vstar M) a0)) ∧
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (concaveClosure (vstar M)) ∧
    (∀ α ∈ Set.Icc (0 : ℝ) 1, vstar M α ≤ concaveClosure (vstar M) α) ∧
    (∀ g : ℝ → ℝ, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g → (∀ α ∈ Set.Icc (0 : ℝ) 1, vstar M α ≤ g α) →
      ∀ α ∈ Set.Icc (0 : ℝ) 1, concaveClosure (vstar M) α ≤ g α) := by sorry

end EngageInfo
