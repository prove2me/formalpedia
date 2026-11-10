-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_7
-- name    : ChaChaTree.DynOpt.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:22:53.453891+00:00
-- url     : https://prove2.me/theorems/14da9784-8259-415e-b5e8-f140ee4939eb
-- title:
--   Lemma 7 — a potential 0 ≤ Φ ≤ 5·IR releasing at least DepthAlt_S on every split
-- statement:
--   There is a function $\Phi$ such that for any instance $P$:
--   1. **Magnitude.** $0 \le \Phi(P) \le 5\,\mathrm{IR}(P)$.
--   2. **Potential release.** For any partition $S$ of the keys into contiguous segments, the split of $P$ with respect to $S$ satisfies $\mathrm{DepthAlt}_S(P) \le \Delta_S \Phi(P)$, where $\Delta_S\Phi(P) := \Phi(P) - (\Phi(\hat P) + \sum_{i\in[k]} \Phi(\check P_i))$.
--
--   One $\Phi$ serves every instance (every $N$, $T$) and every $S$.
--
--   Differences from the source:
--   - encoding: a partition S = (S_1, …, S_k) of [N] into disjoint contiguous intervals ordered from left to right → a segment map seg : ℕ → ℕ with IsSegmentation N k seg (monotone from [N] onto [k]; S_i = {x ∈ [N] | seg x = i}); reason: monotone and onto [k] is exactly a left-to-right partition into k nonempty contiguous intervals; same instances
--   - reading: a function Φ (codomain not stated) → Φ : Finset (ℕ × ℕ) → ℤ; reason: the paper's Φ = Φ₁ + Φ₂ + Φ₃ is integer-valued; an integer-valued Φ is in particular real-valued, so this reading is not weaker
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 7, p. 12 (PDF 13)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles
import Definitions.Def_ChaChaTree_DynOpt_Split

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 7** (p. 12). There is a function `Φ` such that for any instance `P`:
(1) *magnitude* `0 ≤ Φ(P) ≤ 5 IR(P)`; (2) *potential release*: for any partition `S` of the key
range into contiguous segments, `DepthAlt_S(P) ≤ Δ_S Φ(P) = Φ(P) − (Φ(P̂) + Σ_{i∈[k]} Φ(P̌_i))`. -/
theorem lemma_7 :
    ∃ Φ : Finset (ℕ × ℕ) → ℤ, ∀ (N T : ℕ) (P : Finset (ℕ × ℕ)), IsInstance N T P →
      (0 ≤ Φ P ∧ Φ P ≤ 5 * (IR P : ℤ)) ∧
        ∀ (k : ℕ) (seg : ℕ → ℕ), IsSegmentation N k seg →
          (depthAltS seg P : ℤ) ≤ deltaS Φ k seg P := by sorry

end ChaChaTree.DynOpt
