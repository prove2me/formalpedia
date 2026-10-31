-- Prove2me | Theorems.Thm_FairShares_no_feasible_share_dominates_all_sm_feasible
-- name    : FairShares.no_feasible_share_dominates_all_sm_feasible
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:16:45.197861+00:00
-- url     : https://prove2.me/theorems/052bb6e8-5102-42ca-9f1b-5fd7807157a1
-- title:
--   Theorem 1: no feasible share dominates every self-maximizing feasible share
-- statement:
--   Let $\mathcal C$ be a class of valuations that contains all additive valuations over goods (for every number $m$ of goods, $\mathcal C_m$ contains every additive valuation on $m$ goods). Then
--
--   1. there is no share $s$ for $\mathcal C$, feasible for $\mathcal C$, that dominates on $\mathcal C$ every share $s'$ for $\mathcal C$ that is feasible and self-maximizing for $\mathcal C$;
--   2. consequently, there is no SM-dominant feasible share for $\mathcal C$.
--
--   The dominating share $s$ is not required to be self-maximizing, and no computational restriction is imposed on any share. The result covers, for example, the classes of additive, submodular and subadditive valuations.
--
--   Differences from the source:
--   - generalization: C a class of valuations over goods (normalized, non-decreasing) containing all additive valuations → any family C m of functions Finset (Fin m) → ℝ containing every additive valuation; reason: every class of the source satisfies the hypothesis, so the Lean statement implies the source's
--   - encoding: a share s(v, n) for valuations over a set M of items and n agents → s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ, items Fin m, every property quantified over all m and all n ≥ 1; reason: name independence makes Fin m a faithful stand-in for any m-element item set; shares are defined for n ≥ 1 agents
--   - encoding: realizability s(v, n) ≤ max_{S⊆M} v(S) → some bundle S has s m n v ≤ v S; reason: there are finitely many bundles
--   - encoding: name independence, renaming the items does not change the share of v ∈ C → s m n (S ↦ v (σ S)) = s m n v for every permutation σ of Fin m with v and its renaming in C m; reason: a share for C is only defined on C, so the source's condition constrains exactly these pairs
--   - encoding: an allocation (partition into n possibly empty bundles) → A : Fin m → Fin n, agent i's bundle A⁻¹(i); reason: maps to Fin n are exactly the labelled partitions into n possibly empty bundles
--   - encoding: the minimum over acceptable bundles (share guarantee ŝ, implied guarantee ŝ_v(v′)) → Finset.inf in WithTop ℝ over the bundles S with s(v′) ≤ v′(S); reason: for a realizable share the family is nonempty and the value is the real minimum; ⊤ only on an empty family, where the source's minimum is undefined
--   - encoding: SM-dominant: dominates every other feasible self-maximizing share → dominates every feasible self-maximizing share; reason: domination is reflexive
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, Theorem 1, p.14 (restated with proof p.16)

import Mathlib
import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_FairShares_IsShare
import Definitions.Def_FairShares_Feasible
import Definitions.Def_FairShares_SelfMax
import Definitions.Def_FairShares_Dominates
import Definitions.Def_FairShares_IsSMDominantFeasible

namespace FairShares

/-- **Theorem 1: no feasible share dominates all self-maximizing feasible shares.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, Theorem 1, p.14 (restated p.16): "Let C be any class of valuations that contains all
additive valuations over goods. For C, there is no feasible share that dominates all feasible
shares that are self maximizing. Thus, there does not exist an SM-dominant feasible share for
class C."

Let `C` assign to every number `m` of items a set `C m` of valuations on the bundles of `Fin m` that
contains every additive valuation. Then
1. there is no share `s` for `C` that is feasible for `C` and dominates on `C` every share `s'` for
   `C` that is feasible and self-maximizing for `C`;
2. there is no SM-dominant feasible share for `C`.

**Formalization Note.** Shares are `s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ` and every property
quantifies over `n ≥ 1` agents and all `m`. The dominating share `s` is not required to be
self-maximizing. `C` may contain arbitrary real functions on bundles beyond the additive ones (the
paper's classes consist of valuations over goods); realizability is stated with `max_S v(S)`. -/
theorem no_feasible_share_dominates_all_sm_feasible
    (C : (m : ℕ) → Set (Finset (Fin m) → ℝ))
    (hC : ∀ (m : ℕ) (v : Finset (Fin m) → ℝ), IsAdditive v → v ∈ C m) :
    (¬ ∃ s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
        IsShare C s ∧ Feasible C s ∧
          ∀ s' : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
            IsShare C s' → Feasible C s' → SelfMax C s' → Dominates C s s') ∧
      ¬ ∃ s : (m n : ℕ) → (Finset (Fin m) → ℝ) → ℝ, IsSMDominantFeasible C s := by sorry

end FairShares
