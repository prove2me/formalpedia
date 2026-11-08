-- Prove2me | Theorems.Thm_CompDesignBFM_theorem_3_3
-- name    : CompDesignBFM.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:33.242035+00:00
-- url     : https://prove2.me/theorems/06f5d520-7450-4977-8f54-4ac3d8df57e9
-- title:
--   Theorem 3.3 — the potential maximizer approximates OPT
-- statement:
--   Let $v$ be normalized, monotone and subadditive, and let $F$ be normalized, monotone and self-bounding with $\eta v(T)\le F(T)\le v(T)$ for every $T\subseteq N$, for some $\eta\in(0,1]$. Let $B>0$, $c\ge0$, and let $S$ be a global maximizer of $\Phi^F_c$. Then
--
--   1. $v(S)\ge\frac{\eta}{e}(\mathrm{OPT}-M)$;
--   2. if $M\le\theta\,\mathrm{OPT}$ with $0\le\theta<1$, then $v(S)\ge\frac{\eta(1-\theta)}{e}\mathrm{OPT}$;
--   3. if $c_i/B\le l<1$ for all $i$, with $0\le l$, then $v(S)\ge\eta e^{-1/(1-l)}\mathrm{OPT}$.
--
--   These bounds give every ratio of the goal beyond the submodular case.
--
--   Differences from the source:
--   - generalization: S is the global maximizer of Φ^F_c → S is any global maximizer; reason: the bounds hold at every global maximizer, so no tie-breaking is needed; the source's maximizer is an instance
--   - encoding: M/OPT ≤ θ < 1 → M ≤ θ · OPT with 0 ≤ θ < 1; reason: the same condition at OPT > 0, and at OPT = 0 the claim v(S) ≥ 0 is trivial
--   - encoding: M = max{v({i}) : c_i ≤ B} → M is 0 when no agent is affordable; reason: the value of the singleton branch there; the source's maximum is otherwise unchanged
--   - encoding: c_i/B ≤ λ < 1 → c_i/B ≤ l < 1 with 0 ≤ l; reason: 0 ≤ l follows from c ≥ 0 whenever n ≥ 1, and at n = 0 OPT = 0 and the claim is trivial
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem 3.3, p.16 (PDF 18)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSelfBounding
import Definitions.Def_CompDesignBFM_pot
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesignBFM_M
import Definitions.Def_BudgetClock_Subadditive_Setting

namespace CompDesignBFM

/-- Theorem 3.3, Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.16, PDF 18. Let `v` be normalized, monotone and subadditive, and `F` normalized,
monotone and self-bounding with `η v(T) ≤ F(T) ≤ v(T)` for all `T`, for some `η ∈ (0, 1]`. If `S` is a global
maximizer of `Φ^F_c`, then `v(S) ≥ (η/e)(OPT - M)`; if `M ≤ θ OPT` with `0 ≤ θ < 1`, then
`v(S) ≥ (η(1-θ)/e) OPT`; and if `cᵢ/B ≤ l < 1` for all `i`, then `v(S) ≥ η e^(-1/(1-l)) OPT`.
**Formalization Note.** "`M/OPT ≤ θ`" is written `M ≤ θ OPT`: the same condition when `OPT > 0`, and at
`OPT = 0` the claim is trivial. No tie-breaking is needed: the bounds hold at every global maximizer. -/
theorem theorem_3_3 {n : ℕ} (v F : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hsub : BudgetClock.Subadditive.IsSubadditive v)
    (hF0 : F ∅ = 0) (hF : IsSelfBounding F) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hη : ∀ T, η * v T ≤ F T ∧ F T ≤ v T) (hc : ∀ i, 0 ≤ c i)
    (S : Finset (Fin n)) (hS : ∀ T, pot F B c T ≤ pot F B c S) :
    η / Real.exp 1 * (OPT v B c - M v B c) ≤ v S ∧
    (∀ θ : ℝ, 0 ≤ θ → θ < 1 → M v B c ≤ θ * OPT v B c →
      η * (1 - θ) / Real.exp 1 * OPT v B c ≤ v S) ∧
    (∀ l : ℝ, 0 ≤ l → l < 1 → (∀ i, c i / B ≤ l) →
      η * Real.exp (-(1 / (1 - l))) * OPT v B c ≤ v S) := by sorry

end CompDesignBFM
