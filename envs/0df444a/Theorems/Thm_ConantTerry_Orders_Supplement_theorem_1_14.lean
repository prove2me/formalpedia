-- Prove2me | Theorems.Thm_ConantTerry_Orders_Supplement_theorem_1_14
-- name    : ConantTerry.Orders.Supplement.theorem_1_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:26:49.464495+00:00
-- url     : https://prove2.me/theorems/9c6c4b97-0706-4441-9401-67bd277a7c5e
-- title:
--   Theorem 1.14 — extraction of uniform tight ladders
-- statement:
--   Let $k\ge1$, $\delta>0$ and $0<\epsilon<1/2$. The upper restriction is the source's asymptotic convention in §1.6(1). Put $p=\lceil2/\epsilon\rceil$, $n=p^2(k-1)+1$ and $H=\sum_{i=0}^{n-1}p^{2i}$. This positive integer is uniform over every pair of sets $X,Y$ and every $f:X\times Y\to[0,1]$, and it satisfies
--   $$
--   H\le(1/\epsilon)^{54k/\epsilon^2}.
--   $$
--   For every such function,
--   $$
--   f\text{ admits an }(H,2\delta+\epsilon)\text{-tree}\quad\Longrightarrow\quad
--   f\text{ admits a uniform }\epsilon\text{-tight }(k,\delta)\text{-ladder}.
--   $$
--   The paper writes $(1/\epsilon)^{O(k/\epsilon^2)}$; the proof yields the exact height $H$ above and an absolute exponent constant of $54$. Page 18 and footnote 7 are used with the proof parameter $\epsilon/2$, which gives input scale $2\delta+\epsilon$ and even $\epsilon/2$-tightness. The stated conclusion preserves the required $\epsilon$-tightness, the common threshold and the high diagonal.
--
--   This is a companion theorem of the paper, supported here by Lemmas 2.7, 4.2 and 4.3; it is not a step in the proof of the mission's existing goal Theorem 1.11.
--
--   Differences from the source:
--   - encoding: arbitrary sets X,Y and values in [0,1] → arbitrary types X,Y and the real subtype Set.Icc 0 1; reason: the subtype enforces exactly the source range and adds no finiteness, nonemptiness or regularity assumption
--   - encoding: finite binary words and 1-based finite indices → published List Bool word subtypes and zero-based Fin indices; reason: length, prefix, orientation and index inequalities are preserved by relabeling
--   - encoding: intervals in [0,1] of length at most ε → order-convex subsets of Set.Icc 0 1 with every pair at distance at most ε; reason: on the bounded real interval this is exactly the interval length condition, including every endpoint convention and degenerate intervals
--   - encoding: existence of a height t≤(1/ε)^{O(k/ε²)} → the proof-supplied computed H=Σ_{i<n}p^{2i}, with p=ceil(2/ε), n=p²(k−1)+1, its positivity and the bound H≤(1/ε)^{54k/ε²}, before quantification over X,Y,f; reason: p.18 and footnote 7 with parameter ε/2 give this exact height and scale; a=1/ε>2 gives p≤3a≤a³, n≤9ka², H≤p^{2n}≤a^{54ka²}, instantiating the absolute O constant
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p. 6, Theorem 1.14; proof pp. 14–18

import Mathlib
import Definitions.Def_ConantTerry_Orders_function_tree
import Definitions.Def_ConantTerry_Orders_Supplement_uniform_tight_ladders
import Definitions.Def_ConantTerry_Orders_Supplement_extraction_heights

namespace ConantTerry.Orders.Supplement

/-- Theorem 1.14, p.6; exact height from p.18 and footnote 7 with ε/2.
The asymptotic convention 0<ε<1/2 is §1.6(1). The proof's finite sum
satisfies the explicit absolute exponent bound 54*k/ε². Height is computed
before, and independently of, the ambient types and the function. -/
theorem theorem_1_14 (k : ℕ) (hk : 1 ≤ k) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεsmall : ε < 1 / 2) :
    0 < tightHeight k ε ∧
      (tightHeight k ε : ℝ) ≤ (1 / ε : ℝ) ^ (54 * (k : ℝ) / ε ^ 2) ∧
      ∀ {X : Type*} {Y : Type*} (f : X × Y → Set.Icc (0 : ℝ) 1),
        AdmitsTree f (tightHeight k ε) (2 * δ + ε) →
          AdmitsTightLadder f k δ ε := by sorry

end ConantTerry.Orders.Supplement
