-- Prove2me | Theorems.Thm_CompDesignBFM_theorem_3_2
-- name    : CompDesignBFM.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:19.448017+00:00
-- url     : https://prove2.me/theorems/df087896-3863-4c93-80a3-8592a22d1308
-- title:
--   Theorem 3.2 — potential maximizers are pure Nash equilibria
-- statement:
--   Let $F$ be normalized and monotone, $B>0$ and $c\ge0$. If $S$ is a global maximizer of the potential $\Phi^F_c$, with $S=\emptyset$ or $\Phi^F_c(S)>0$, then $S$ is a pure Nash equilibrium of the marginal-contribution rule.
--
--   This is what makes the potential maximizer an equilibrium allocation, and the mechanism's budget feasibility rests on it.
--
--   Differences from the source:
--   - reading: the global maximizer S of Φ^F_c → a global maximizer with S = ∅ or Φ^F_c(S) > 0; reason: uniqueness needs the Remark 2.1 tie-breaking with ∅ first, whose maximizer has this property, and the printed proof says 'Now suppose S ≠ ∅. Then Φ(S) > 0'. Without it F ≡ 0, n = 1, B = 1, c₁ = 1/2, S = {1} fails
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem 3.2, p.15 (PDF 17)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_pot

namespace CompDesignBFM

/-- Theorem 3.2, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.15, PDF 17. For a normalized monotone `F`, the global maximizer of `Φ^F_c` is a
pure Nash equilibrium of the marginal-contribution rule.
**Formalization Note.** "The global maximizer" is the one of Remark 2.1, with `∅` first, whose potential
is positive unless it is `∅`; the printed proof says "Now suppose `S ≠ ∅`. Then `Φ^F_c(S) > 0`". That
property is the hypothesis `hS₀`. Without it `F ≡ 0`, `n = 1`, `B = 1`, `c₁ = 1/2`, `S = {1}` fails. -/
theorem theorem_3_2 {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hF0 : F ∅ = 0) (hF : IsMonotoneSF F) (hc : ∀ i, 0 ≤ c i) (S : Finset (Fin n))
    (hS : ∀ T, pot F B c T ≤ pot F B c S) (hS₀ : S = ∅ ∨ 0 < pot F B c S) :
    IsPNE F B c S := by sorry

end CompDesignBFM
