-- Prove2me | Theorems.Thm_AlmostMMS_theorem_1_1
-- name    : AlmostMMS.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:58.724129+00:00
-- url     : https://prove2.me/theorems/f9fcf230-849e-4dc3-8331-127e0c82ce04
-- title:
--   Theorem 1.1 — among any $(1+\varepsilon)n$ agents, some $n$ have a $\rho$-MMS($n$) allocation
-- statement:
--   For every $\varepsilon>0$ and $\rho<1$ there is $n_{\varepsilon,\rho}$ such that for every $n\ge n_{\varepsilon,\rho}$ the following holds. In every allocation instance with additive valuations, $m$ items and $D\ge(1+\varepsilon)n$ agents, there is a set $I$ of $n$ agents and an allocation of all the items to $I$ with
--   $$
--   v_i(A_i)\ge\rho\cdot\mathrm{MMS}(M,v_i,n)\qquad\text{for every } i\in I.
--   $$
--   The benchmark is the maximin share for $n$ parts, not for the larger agent count $D$, and the ratio between the two can be unbounded. The threshold depends only on $\varepsilon$ and $\rho$. This is the paper's main result: the conjecture that $\rho$-MMS allocations exist for all large $n$ holds in the setting with agent redundancy.
--
--   **Formalization Note** The page calls the agent count $d$; the Lean binder is `D`, since from Section 1.2 on the paper swaps the letters.
--
--   Differences from the source:
--   - generalization: ρ-MMS is defined for ρ ∈ (0, 1] (p.1) → every real ρ < 1, as Theorem 1.1 itself prints; reason: for ρ ≤ 0 the conclusion follows at once from nonnegativity; ρ ∈ (0, 1) is the source's claim
--   - encoding: additive valuations with v(∅) = 0, monotone → the published `LittleCharity.MMS.IsAdditive` (additivity and nonnegativity); reason: equivalent for additive set functions
--   - encoding: an allocation as a partition of M → a map A from items into I, with bundle A⁻¹(i); reason: same partitions; every item goes to an agent of I
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_ImprovedMMS_Additive_Instance

namespace AlmostMMS

open Finset

/-- **Theorem 1.1, p.2.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): for every `ε > 0` and `ρ < 1` there is `n_{ε,ρ}` such
that for every `n ≥ n_{ε,ρ}`, in every instance with additive valuations and `d ≥ (1 + ε) n` agents,
some `n` agents have a `ρ`-MMS(`n`) allocation.

**Formalization Note.** This is §1.1's lettering: `n` agents are selected, and the agent count (the
paper's `d`) is `D`. `AdmitsMMSAlloc ρ v I univ` allocates every item to an agent of `I` and benchmarks
agent `i` against `mms (v i) I.card univ`, which here is the share for `n` parts, not `D` parts. `n₀` is
chosen after `ε, ρ` and before `n, D, m, v`. -/
theorem theorem_1_1 (ε ρ : ℝ) (hε : 0 < ε) (hρ : ρ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (D m : ℕ) (v : Fin D → Finset (Fin m) → ℝ),
      LittleCharity.MMS.IsAdditive v → (1 + ε) * (n : ℝ) ≤ (D : ℝ) →
      ∃ I : Finset (Fin D), I.card = n ∧
        ImprovedMMS.Additive.AdmitsMMSAlloc ρ v I Finset.univ := by sorry

end AlmostMMS
