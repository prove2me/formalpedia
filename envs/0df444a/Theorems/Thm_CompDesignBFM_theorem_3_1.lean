-- Prove2me | Theorems.Thm_CompDesignBFM_theorem_3_1
-- name    : CompDesignBFM.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:28.271964+00:00
-- url     : https://prove2.me/theorems/d9d86f66-5ea8-4aa4-957c-633b36fcc9c2
-- title:
--   Theorem 3.1 (corrected: local maximizers need S = ∅ or positive potential) — equilibria and OPT ≤ M + 2v(S)
-- statement:
--   Let $v$ be normalized, monotone and submodular, $B>0$ and $c\ge0$.
--
--   1. Every local maximizer $S$ of $\Phi^v_c$ with $S=\emptyset$ or $\Phi^v_c(S)>0$ is a pure Nash equilibrium of the marginal-contribution game.
--   2. For any pure Nash equilibrium $S$,
--
--   $$\mathrm{OPT}\le M+2v(S).$$
--
--   This is the bound behind the ratio 3 for monotone submodular values.
--
--   Differences from the source:
--   - correction: every local maximizer S ⊆ N of Φ^v_c is a pure Nash equilibrium → every local maximizer with S = ∅ or Φ^v_c(S) > 0; reason: the printed clause is false: n = 1, B = 1, c₁ = 1/2, v ≡ 0, S = {1} has Φ ≡ 0, so S is a local maximizer, and p₁(S) = 0 < c₁
--   - reading: local maximizer (undefined in the source) → adding or removing any one agent does not increase Φ; reason: these are the deviations of the game, and the weakest notion gives the strongest statement
--   - encoding: M = max{v({i}) : c_i ≤ B} → M is 0 when no agent is affordable; reason: the value of the singleton branch there; the source's maximum is otherwise unchanged
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem 3.1, p.13 (PDF 15)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_pot
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesignBFM_M

namespace CompDesignBFM

/-- Theorem 3.1, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.13, PDF 15, with its first clause corrected. Every local maximizer `S` of `Φ^v_c`
with `S = ∅` or `Φ^v_c(S) > 0` is a pure Nash equilibrium of the marginal-contribution game, and every pure
Nash equilibrium `S` satisfies `OPT ≤ M + 2 v(S)`.
**Formalization Note.** As printed the first clause is false: for `n = 1`, `B = 1`, `c₁ = 1/2`, `v ≡ 0`, the
set `S = {1}` is a local maximizer (`Φ = 0` everywhere) and `p₁(S) = 0 < c₁`. A local maximizer is one that
adding or removing a single agent does not improve. -/
theorem theorem_3_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i) :
    (∀ S : Finset (Fin n),
      (∀ i, pot v B c (insert i S) ≤ pot v B c S ∧ pot v B c (S.erase i) ≤ pot v B c S) →
      (S = ∅ ∨ 0 < pot v B c S) → IsPNE v B c S) ∧
    ∀ S : Finset (Fin n), IsPNE v B c S → OPT v B c ≤ M v B c + 2 * v S := by sorry

end CompDesignBFM
