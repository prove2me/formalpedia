-- Prove2me | Theorems.Thm_FiniteMemPOMDP_lemma_A_8
-- name    : FiniteMemPOMDP.lemma_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:18.000661+00:00
-- url     : https://prove2.me/theorems/7bb0b437-4221-4239-8935-ce3475c7f930
-- title:
--   Lemma A.8 ([27, Lemma 33]) — invariant measure and occupation measures
-- statement:
--   Let $\Gamma$ be a finite POMDP and $p_1\in\Delta(\mathcal K)$. There exist a probability measure $\mu^*\in\Delta(\Delta(\mathcal K))$ and a measurable (mixed) stationary strategy $\sigma^*:\Delta(\mathcal K)\to\Delta(\mathcal A)$ such that:
--
--   1. $\mu^*$ is $\sigma^*$-invariant;
--   2. for all $\varepsilon>0$ and $N\ge1$ there are $n_\varepsilon\ge N$ and a pure strategy $\sigma^\varepsilon$ that is $0$-optimal in the $n_\varepsilon$-stage game $\Gamma_{n_\varepsilon}(p_1)$ and satisfies
--   $$d_{KR}\Big(\frac1{n_\varepsilon}\sum_{m=1}^{n_\varepsilon}z_m[p_1,\sigma^\varepsilon],\ \mu^*\Big)\le\varepsilon;$$
--   3. $$\int_{\Delta(\mathcal K)}g(p,\sigma^*(p))\,\mu^*(dp)=\int_{\Delta(\mathcal K)}v_\infty(p)\,\mu^*(dp)=v_\infty(p_1).$$
--
--   This is Venel and Ziliotto's lemma as restated by the paper; the paper derives Lemma 5.3 from it.
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
--   - reading: E1 = 1-Lipschitz functions from ∆(K) to [0,1], metric on ∆(K) unspecified → 1-Lipschitz for ‖p − p′‖₁ = ∑_k |p(k) − p′(k)|; reason: the norm of Lemma 5.3; it gives the largest E1 and so the strongest bound d_KR ≤ ε among the usual norms
--   - encoding: σε 0-optimal in Γnε(p1); (1/nε)∑_{m=1}^{nε} z_m[p1, σε] → gammaN Γ nε p1 σε = vN Γ nε p1; (1/nε) • ∑_{m ∈ range nε} occMeasure Γ p1 σε m (occMeasure … m is z_{m+1}); reason: definition of 0-optimality; stage index shifted by one
--   - encoding: z_m[µ, σ] the law of P_m for µ ∈ ∆(∆(K)); E[f(q̃[p, σ(p)])]; g(p, σ*(p)) → occMeasure, the finite sum over histories h of P(H = h) δ_{belief h}, for µ = δ_{p1} only; ∑_a σs(p)(a) ∫ f dq̃[p, a] with q̃[p, a] = ∑_s P_{p,a}(s) δ_{bayes(p,a,s)}; mixedReward = ∑_k ∑_a p(k) σs(p)(a) g(k, a); reason: the same objects: each H_m takes finitely many values, Lemma A.8 only uses µ = δ_{p1}, and the paper leaves the expectation and the linear extension of g implicit
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Lemma A.8, p.24

import Mathlib
import Definitions.Def_FiniteMemPOMDP_vN
import Definitions.Def_FiniteMemPOMDP_vInf
import Definitions.Def_FiniteMemPOMDP_IsInvariant
import Definitions.Def_FiniteMemPOMDP_mixedReward
import Definitions.Def_FiniteMemPOMDP_occMeasure
import Definitions.Def_FiniteMemPOMDP_dKR

open MeasureTheory

namespace FiniteMemPOMDP

/-- **Lemma A.8 ([27, Lemma 33]) — invariant measure and occupation measures.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Lemma A.8, p.24: "Consider a POMDP Γ and let
p1 ∈ ∆(K). There exists µ∗ ∈ ∆(∆(K)) and a (mixed) stationary strategy σ∗: ∆(K) → ∆(A) such that
1. µ∗ is σ∗-invariant.
2. For all ε > 0 and N ≥ 1, there exists nε ≥ N and σε a pure strategy in Γ such that σε is
0-optimal in the nε-stage game Γnε(p1) and dKR((1/nε) ∑_{m=1}^{nε} zm[p1, σε], µ∗) ≤ ε.
3. ∫_{∆(K)} g(p, σ∗(p))µ∗(dp) = ∫_{∆(K)} v∞(p)µ∗(dp) = v∞(p1)."

The statement: there are a probability measure `μ` on `∆(K)` and a measurable
`σs : ∆(K) → ∆(A)` such that (1) `μ` is `σs`-invariant, (2) for every `ε > 0` and `N ≥ 1`
there are `nε ≥ N` and a pure strategy `σε` with `γ^{p1}_{nε}(σε) = v_{nε}(p1)` and
`d_KR((1/nε) ∑_{m=1}^{nε} z_m[p1, σε], μ) ≤ ε`, and (3)
`∫ g(p, σs(p)) μ(dp) = ∫ v∞ dμ = v∞(p1)`.

**Formalization Note** "`σε` is 0-optimal in `Γ_{nε}(p1)`" is `gammaN Γ nε p1 σε = vN Γ nε p1`.
`z_m[p1, σε]` is `occMeasure Γ p1 σε (m − 1)`, so the sum over `m = 1, …, nε` is the sum over
`Finset.range nε`. The measurability of `σ∗` is the one required by Definition A.3. The metric of
`d_KR` is `‖·‖₁` (see `dKR`). `v∞` is continuous (Remark A.4, p.23), so `∫ v∞ dμ` is a genuine
integral. -/
theorem lemma_A_8 {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (p1 : stdSimplex ℝ K) :
    ∃ (μ : Measure (stdSimplex ℝ K)) (σs : stdSimplex ℝ K → stdSimplex ℝ A),
      IsProbabilityMeasure μ ∧ Measurable σs ∧
      IsInvariant Γ σs μ ∧
      (∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N → ∃ nε : ℕ, N ≤ nε ∧ ∃ σε : List (A × S) → A,
        gammaN Γ nε p1 σε = vN Γ nε p1 ∧
        dKR ((1 / (nε : ENNReal)) • ∑ m ∈ Finset.range nε, occMeasure Γ p1 σε m) μ ≤ ε) ∧
      ∫ p, mixedReward Γ σs p ∂μ = ∫ p, vInf Γ p ∂μ ∧
      ∫ p, vInf Γ p ∂μ = vInf Γ p1 := by sorry

end FiniteMemPOMDP
