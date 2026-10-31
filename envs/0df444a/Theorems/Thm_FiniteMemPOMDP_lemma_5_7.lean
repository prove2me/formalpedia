-- Prove2me | Theorems.Thm_FiniteMemPOMDP_lemma_5_7
-- name    : FiniteMemPOMDP.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:12.848191+00:00
-- url     : https://prove2.me/theorems/81a1e3d5-46a9-4722-8d5c-f86d999a95e4
-- title:
--   Lemma 5.7 — an ergodic strategy can be replaced by a finite-memory one
-- statement:
--   Let $p^*\in\Delta(\mathcal K)$ and let $\sigma$ be an ergodic strategy for $p^*$. For every $\varepsilon>0$ there exists a finite-memory strategy $\sigma'$ such that
--
--   $$\gamma^{p^*}_\infty(\sigma')\ge\gamma^{p^*}_\infty(\sigma)-\varepsilon .$$
--
--   This is the paper's key lemma; with Lemma 5.3 it gives Theorem 2.9.
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
--   - encoding: σ = (σu, σa, M, m0) with M a finite set → ∃ M : Type with Finite M, m0, σa, σu generating σ by a left fold over the history; reason: the standard transducer semantics, which the paper leaves implicit
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Lemma 5.7, p.14

import Mathlib
import Definitions.Def_FiniteMemPOMDP_IsErgodic
import Definitions.Def_FiniteMemPOMDP_IsFiniteMemory

namespace FiniteMemPOMDP

/-- **Lemma 5.7 — an ergodic strategy can be replaced by a finite-memory one.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Lemma 5.7, p.14: "Let p∗ ∈ ∆(K) and σ be an
ergodic strategy for p∗. For all ε > 0, there exists a finite-memory strategy σ′ such that
γ^{p∗}_∞(σ′) ≥ γ^{p∗}_∞(σ) − ε."

For every belief `p∗`, every strategy `σ` that is ergodic for `p∗` (Definition 5.6) and every
`ε > 0`, some finite-memory strategy `σ′` (Definition 2.5) has
`γ^{p∗}_∞(σ′) ≥ γ^{p∗}_∞(σ) − ε`. -/
theorem lemma_5_7 {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A) (hσ : IsErgodic Γ p σ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ σ' : List (A × S) → A, IsFiniteMemory σ' ∧ gammaInf Γ p σ - ε ≤ gammaInf Γ p σ' := by sorry

end FiniteMemPOMDP
