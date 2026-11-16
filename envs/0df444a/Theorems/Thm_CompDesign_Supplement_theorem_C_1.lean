-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_C_1
-- name    : CompDesign.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:02:47.689789+00:00
-- url     : https://prove2.me/theorems/521d7bd1-7c1c-4a12-a8e4-71f0dc90845d
-- title:
--   Theorem C.1 — targeted implementation (58): the pure Nash equilibria are exactly $\{T\}$ and every CCE is supported on $T$
-- statement:
--   Throughout, $N=\{1,\dots,n\}$ is the set of agents, $B>0$ the budget and $c_i\ge0$ the private costs. Let $T\subseteq N$ be a target set with bonuses $b_i>0$ ($i\in T$) such that $\sum_{i\in T}(c_i+b_i)\le B$ (57), and let $p_i(S)=c_i+b_i$ if $i\in S\cap T$ and $0$ otherwise (58).
--
--   **Theorem C.1 (Targeted implementation with outsider exclusion).** Suppose $c_i>0$ for every $i\notin T$. Under the rule (58),
--
--   1. a set $S$ is a pure Nash equilibrium if and only if $S=T$;
--   2. every coarse correlated equilibrium $\mu$ is supported on $T$: $\mu(S)=0$ for every $S\ne T$.
--
--   When costs are known, any target set, for instance the output of an approximation algorithm for non-monotone submodular maximization, can be implemented exactly.
--
--   Differences from the source:
--   - generalization: every pure Nash equilibrium is exactly T → S is a pure Nash equilibrium iff S = T; reason: adds that T is an equilibrium, which the proof shows (T is the unique dominant profile); the forward direction is the source's claim
--   - encoding: supported on the single set T → μ(S) = 0 for every S ≠ T; reason: the support of a weight function
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem C.1, App. C, p.71 (PDF 74)

import Mathlib
import Definitions.Def_CompDesign_Supplement_IsPNEOf
import Definitions.Def_CompDesign_Supplement_IsCCEOf
import Definitions.Def_CompDesign_Supplement_targetedPay

set_option autoImplicit false

namespace CompDesign.Supplement

/-- Theorem C.1 (Targeted implementation with outsider exclusion), App. C, p.71 (PDF 74) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…).
Suppose that every non-target agent has strictly positive cost: `c_i > 0` for all `i ∉ T`. Under the
payment rule (58), every pure Nash equilibrium is exactly `T`. Moreover, every coarse correlated
equilibrium is supported on the single set `T`.

**Formalization Note.** The target `T` comes with bonuses `b_i > 0` (`i ∈ T`) satisfying (57),
`∑_{i∈T} (c_i + b_i) ≤ B`. The first clause is stated as an equivalence (`S` is a pure Nash
equilibrium iff `S = T`), since the proof shows `T` is the unique dominant profile. "Supported on `T`"
is `μ(S) = 0` for every `S ≠ T`. No value function is involved. -/
theorem theorem_C_1 {n : ℕ} (B : ℝ) (hB : 0 < B) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (T : Finset (Fin n)) (b : Fin n → ℝ) (hb : ∀ i ∈ T, 0 < b i)
    (hbud : ∑ i ∈ T, (c i + b i) ≤ B) (hout : ∀ i, i ∉ T → 0 < c i) :
    (∀ S : Finset (Fin n), IsPNEOf (targetedPay T c b) c S ↔ S = T) ∧
    ∀ μ : Finset (Fin n) → ℝ, IsCCEOf (targetedPay T c b) c μ → ∀ S, S ≠ T → μ S = 0 := by sorry

end CompDesign.Supplement
