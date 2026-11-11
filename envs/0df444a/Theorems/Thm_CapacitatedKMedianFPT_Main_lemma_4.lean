-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_lemma_4
-- name    : CapacitatedKMedianFPT.Main.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:30.845741+00:00
-- url     : https://prove2.me/theorems/da41b1dd-7d40-4856-8f1d-94e30d56b98b
-- title:
--   Lemma 4 — Z ≤ 3·OPT(1 + O(ε))
-- statement:
--   In the setting of Lemma 3, let $(O^\star,\varphi^\star)$ be an optimal solution with $n_i\ge1$, suppose the leaders and radii satisfy (3.2) and (3.3), and suppose $o^\star_i\in F_i$ for every $i$. Then the proxy cost of the optimal assignment,
--   $$Z=\sum_{c\in C}\tilde d(c,\varphi^\star(c)),$$
--   satisfies
--   $$Z\le3\cdot\mathrm{OPT}\,(1+O(\varepsilon)).$$
--
--   The constant in $O(\varepsilon)$ is absolute (the proof gives $Z\le(1+2\varepsilon)(3+10\varepsilon)\mathrm{OPT}$).
--
--   Differences from the source:
--
--   - encoding: O(ε) → C₀·ε with one absolute constant C₀ chosen before all instances; reason: the meaning of O with a universal constant
--   - generalization: the branch fixed by the enumeration: (ℓ, r̃) an entry of L, χ from an k-perfect family, h(c) = argmin with the source's ties → any leaders that are clients, any radii in ℕ, any coloring χ : P → [k], any permutation π and any nearest-leader choice h; reason: the statement uses only these properties; the source's branch is one instance
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 11, Lemma 4 and proof; p. 9, assumptions of the guessed branch (Lemma 2 conditions, o⋆_i ∈ F_i)

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Proxy

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

/-- **Lemma 4** (p. 11). In the branch where the leaders and radii satisfy (3.2) and (3.3) for the
optimal solution `(O⋆, φ⋆)` and `o⋆_i ∈ F_i` for every `i`, the proxy cost
`Z = ∑_c d̃(c, φ⋆(c))` satisfies `Z ≤ 3 · OPT · (1 + O(ε))`, with one absolute constant `C₀`. -/
theorem lemma_4 :
    ∃ C₀ : ℝ, ∀ {P : Type} [Fintype P] [DecidableEq P] (I : Instance P) (ε : ℝ) (G : Guess I)
      (o : Fin I.k → P) (φs : P → P),
      I.IsValid → 0 < ε → ε < 1 / 2 → I.HasIntDistancesUpTo (distanceBound I.size ε) →
      (∀ i, G.ℓ i ∈ I.C) → G.IsNearestLeader →
      I.IsIndexedOptimum o φs → (∀ i, 1 ≤ I.load φs (o i)) →
      ∑ i, (I.load φs (o i) : ℝ) * I.d (o i) (G.ℓ i) ≤ (1 + 2 * ε) * I.cost φs →
      ∑ i, (I.load φs (o i) : ℝ) * (G.r i : ℝ) ≤ (1 + 5 * ε) * I.cost φs →
      (∀ i, o i ∈ G.group i) →
      G.proxyOpt ε φs ≤ 3 * I.cost φs * (1 + C₀ * ε) := by sorry

end CapacitatedKMedianFPT.Main
