-- Prove2me | Theorems.Thm_FiniteMemPOMDP_remark_A_2
-- name    : FiniteMemPOMDP.remark_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:57.926191+00:00
-- url     : https://prove2.me/theorems/c4b49b9e-b449-4372-8583-81e7255650be
-- title:
--   Remark A.2 — $v_n\to v_\infty$ uniformly on $\Delta(\mathcal K)$
-- statement:
--   Let $\Gamma$ be a finite POMDP. The values $v_n$ of the $n$-stage games converge to the long-run value $v_\infty$ uniformly on $\Delta(\mathcal K)$: for every $\varepsilon>0$ there is $N$ such that
--
--   $$|v_n(p)-v_\infty(p)|\le\varepsilon\qquad\text{for all } n\ge N \text{ and all } p\in\Delta(\mathcal K).$$
--
--   The paper attributes this to Venel and Ziliotto [27]. It is the first input of the proof of Lemma 5.3.
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Remark A.2, p.23

import Mathlib
import Definitions.Def_FiniteMemPOMDP_vN
import Definitions.Def_FiniteMemPOMDP_vInf

namespace FiniteMemPOMDP

/-- **Remark A.2 — `v_n → v∞` uniformly on `∆(K)`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Remark A.2, p.23: "As the notation suggests, it
was proven in [27] that for any finite POMDP (vn) −→_{n→∞} v∞ uniformly."

For every finite POMDP and every `ε > 0` there is `N` such that `|v_n(p) − v∞(p)| ≤ ε` for all
`n ≥ N` and all beliefs `p`. -/
theorem remark_A_2 {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ p : stdSimplex ℝ K, |vN Γ n p - vInf Γ p| ≤ ε := by sorry

end FiniteMemPOMDP
