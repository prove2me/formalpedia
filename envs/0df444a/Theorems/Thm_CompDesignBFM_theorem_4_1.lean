-- Prove2me | Theorems.Thm_CompDesignBFM_theorem_4_1
-- name    : CompDesignBFM.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:49.610446+00:00
-- url     : https://prove2.me/theorems/8ae6d546-67c4-4b62-aaff-a71e108f6e59
-- title:
--   Theorem 4.1 — universally truthful budget-feasible mechanisms with ratios 3, e + 1, 2e + 1, and limits 2, e, 2e in large markets
-- statement:
--   For every number of agents $n$, every budget $B>0$ and every value function $v$ in the class, there exists a universally truthful, individually rational, budget-feasible randomized mechanism such that for every cost vector $c\ge0$,
--
--   $$\mathrm{OPT}(v,B,c)\le\rho\,\mathbb E[v(S(c))],$$
--
--   where
--
--   1. $\rho=3$ when $v$ is monotone submodular;
--   2. $\rho=e+1$ when $v$ is (nonmonotone) XOS;
--   3. $\rho=2e+1$ when $v$ is (nonmonotone) subadditive.
--
--   In the large-market setting each mechanism is deterministic: there is a function $g$ with $g(l)\to L$ as $l\to0^+$, fixed before $n$, $B$ and $v$, and for every $n$, $B$ and $v$ in the class a truthful, individually rational, budget-feasible deterministic mechanism such that for every $l\in(0,1)$ and every $c$ with $0\le c_i\le lB$,
--
--   $$\mathrm{OPT}(v,B,c)\le g(l)\,v(S(c)),$$
--
--   where
--
--   4. $L=2$ when $v$ is monotone submodular;
--   5. $L=e$ when $v$ is (nonmonotone) XOS;
--   6. $L=2e$ when $v$ is (nonmonotone) subadditive.
--
--   Value functions are normalized and nonnegative. The mechanism may depend on $n$, $B$ and $v$ but never on the costs, and it pays nonnegative amounts only to selected agents.
--
--   **Formalization Note** XOS functions are normalized by the empty sum. Monotone normalized functions and subadditive functions are automatically nonnegative, so only the XOS clauses state nonnegativity.
--
--   Differences from the source:
--   - encoding: a randomized mechanism is a distribution over deterministic mechanisms → a finite mixture with real weights; reason: a finite mixture is such a distribution, so the existence claim is at least as strong
--   - reading: 2 + o_λ(1), e + o_λ(1), 2e + o_λ(1), with λ = max c_i/B → a rate g fixed before n, B, v, with g(l) → L as l → 0⁺, and OPT ≤ g(l) · v(S(c)) whenever c_i ≤ lB; reason: the strongest reading: uniform over all instances, and the mechanism does not depend on l
--   - reading: there exist mechanisms 'when v is' in the class → for every n, B, v there is a mechanism, chosen before the costs; reason: the mechanism may depend on v and B (the paper's RMC does) and is cost-oblivious
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem 4.1, p.22 (PDF 24)

import Mathlib
import Definitions.Def_CompDesignBFM_Mechanism
import Definitions.Def_CompDesignBFM_IsGood
import Definitions.Def_CompDesignBFM_RandMechanism
import Definitions.Def_CompDesignBFM_IsUniversallyGood
import Definitions.Def_CompDesignBFM_expectedValue
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsXOS
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_BudgetClock_Subadditive_Setting
open Filter Topology

namespace CompDesignBFM

/-- Theorem 4.1, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.22, PDF 24. There exist universally truthful, individually rational, budget-feasible
mechanisms with approximation ratio `3` for monotone submodular `v`, `e + 1` for (nonmonotone) XOS `v` and `2e + 1`
for (nonmonotone) subadditive `v`. In the large-market setting each mechanism is deterministic and attains ratio
`2 + o_λ(1)`, `e + o_λ(1)` and `2e + o_λ(1)` respectively.
**Formalization Note.** The value function is normalized and nonnegative throughout (p.1, p.40); XOS gives
`v ∅ = 0` from the empty sum, monotone normalized gives nonnegativity, and subadditivity gives it from
`v S = v (S ∪ S) ≤ 2 v S`, so those clauses need no separate nonnegativity hypothesis. The mechanism is chosen after `n, B, v`
and before the costs. In clauses 4–6 the rate `g` is chosen before `n, B, v`, the mechanism before `l` and `c`, and
`cᵢ ≤ l B` for all `i` is `λ = max cᵢ/B ≤ l`, so the `o_λ(1)` is uniform over all instances. -/
theorem theorem_4_1 :
    (∀ (n : ℕ) (B : ℝ) (v : Finset (Fin n) → ℝ), 0 < B → v ∅ = 0 → IsMonotoneSF v → IsSubmodularSF v →
      ∃ R : RandMechanism n, IsUniversallyGood B R ∧
        ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → OPT v B c ≤ 3 * expectedValue R v c) ∧
    (∀ (n : ℕ) (B : ℝ) (v : Finset (Fin n) → ℝ), 0 < B → (∀ S, 0 ≤ v S) → IsXOS v →
      ∃ R : RandMechanism n, IsUniversallyGood B R ∧
        ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → OPT v B c ≤ (Real.exp 1 + 1) * expectedValue R v c) ∧
    (∀ (n : ℕ) (B : ℝ) (v : Finset (Fin n) → ℝ), 0 < B → v ∅ = 0 →
      BudgetClock.Subadditive.IsSubadditive v →
      ∃ R : RandMechanism n, IsUniversallyGood B R ∧
        ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → OPT v B c ≤ (2 * Real.exp 1 + 1) * expectedValue R v c) ∧
    (∃ g : ℝ → ℝ, Tendsto g (𝓝[>] 0) (𝓝 2) ∧
      ∀ (n : ℕ) (B : ℝ) (v : Finset (Fin n) → ℝ), 0 < B → v ∅ = 0 → IsMonotoneSF v → IsSubmodularSF v →
        ∃ m : Mechanism n, IsGood B m ∧ ∀ l : ℝ, 0 < l → l < 1 → ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) →
          (∀ i, c i ≤ l * B) → OPT v B c ≤ g l * v (m.alloc c)) ∧
    (∃ g : ℝ → ℝ, Tendsto g (𝓝[>] 0) (𝓝 (Real.exp 1)) ∧
      ∀ (n : ℕ) (B : ℝ) (v : Finset (Fin n) → ℝ), 0 < B → (∀ S, 0 ≤ v S) → IsXOS v →
        ∃ m : Mechanism n, IsGood B m ∧ ∀ l : ℝ, 0 < l → l < 1 → ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) →
          (∀ i, c i ≤ l * B) → OPT v B c ≤ g l * v (m.alloc c)) ∧
    (∃ g : ℝ → ℝ, Tendsto g (𝓝[>] 0) (𝓝 (2 * Real.exp 1)) ∧
      ∀ (n : ℕ) (B : ℝ) (v : Finset (Fin n) → ℝ), 0 < B → v ∅ = 0 →
        BudgetClock.Subadditive.IsSubadditive v →
        ∃ m : Mechanism n, IsGood B m ∧ ∀ l : ℝ, 0 < l → l < 1 → ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) →
          (∀ i, c i ≤ l * B) → OPT v B c ≤ g l * v (m.alloc c)) := by sorry

end CompDesignBFM
