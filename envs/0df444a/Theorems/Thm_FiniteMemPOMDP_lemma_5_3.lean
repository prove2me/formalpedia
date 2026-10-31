-- Prove2me | Theorems.Thm_FiniteMemPOMDP_lemma_5_3
-- name    : FiniteMemPOMDP.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:33:18.641295+00:00
-- url     : https://prove2.me/theorems/7c0f765b-2014-450f-83ec-df918c3eff1c
-- title:
--   Lemma 5.3 — a belief with an ergodic optimal strategy is reached
-- statement:
--   For every initial belief $p_1$ and every $\varepsilon>0$ there exist $m_\varepsilon\ge1$, a strategy $\sigma^\varepsilon$ and a random belief $P^*\in\Delta(\mathcal K)$, a function of the history $H_{m_\varepsilon}$ before stage $m_\varepsilon$, such that:
--
--   1. $$\mathbb P^{p_1}_{\sigma^\varepsilon}\big(\|P_{m_\varepsilon}-P^*\|_1\le\varepsilon\big)\ge1-\varepsilon,$$ where $P_{m_\varepsilon}$ is the belief at stage $m_\varepsilon$;
--   2. for every value of $P^*$ there is a strategy $\sigma$ that is ergodic for $P^*$, i.e. for every $k\in\operatorname{supp}(P^*)$, $\frac1n\sum_{m=1}^nG_m\to\gamma^k_\infty(\sigma)$ $\mathbb P^k_\sigma$-a.s., and moreover $\gamma^{P^*}_\infty(\sigma)=v_\infty(P^*)$;
--   3. $$\mathbb E^{p_1}_{\sigma^\varepsilon}\big(v_\infty(P^*)\big)\ge v_\infty(p_1)-\varepsilon .$$
--
--   This is the first of the two lemmas from which the paper derives Theorem 2.9.
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
--   - encoding: mε ≥ 1, P* a function of H_{mε} → mε = n + 1 with n : ℕ; Pstar : List (A × S) → ∆(K) applied to historyAt n ω (a list of length n = mε − 1); reason: same index set; histories indexed by length
--   - encoding: property 2 for the realized values of P* → property 2 for every history h of length n; reason: equivalent: Pstar can be redefined on histories of probability zero (to a value taken on a positive-probability history) without changing properties 1 and 3
--   - encoding: ‖P_{mε} − P*‖₁; P_m(k) = P(K_m = k | H_m) → ∑_k |belief Γ p1 σε (historyAt n ω) k − Pstar(historyAt n ω) k|; belief = P(H = h, K = k)/∑_k′ P(H = h, K = k′); reason: the same quantity on every history of positive probability; the event is measured up to null sets
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Lemma 5.3, p.13

import Mathlib
import Definitions.Def_FiniteMemPOMDP_belief
import Definitions.Def_FiniteMemPOMDP_IsErgodic
import Definitions.Def_FiniteMemPOMDP_vInf

open MeasureTheory

namespace FiniteMemPOMDP

/-- **Lemma 5.3 — reaching a belief with an ergodic optimal strategy.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Lemma 5.3, p.13: "For any initial belief p1 and
ε > 0, there exists mε ≥ 1, σε ∈ Σ and a (random) belief P∗ ∈ ∆(K) (which depends on the history
before stage mε) such that:
1. P^{p1}_{σε}(∥Pmε − P∗∥1 ≤ ε) ≥ 1 − ε.
2. There exists σ ∈ Σ, which depends on P∗, such that for all k ∈ supp(P∗)
((1/n) ∑_{m=1}^n Gm) −→_{n→∞} γ^k_∞(σ)  P^k_σ − a.s.
Moreover, γ^{P∗}_∞(σ) = v∞(P∗) and E^{p1}_{σε}(v∞(P∗)) ≥ v∞(p1) − ε."

Here `mε = n + 1`: the random belief `P∗` is a function `Pstar` of the history
`H_{mε} = historyAt n ω` (a list of length `n`), and `P_{mε}` is `belief Γ p1 σε (historyAt n ω)`.
Property 2 is "σ is ergodic for `P∗`" (Definition 5.6) together with
`γ^{P∗}_∞(σ) = v∞(P∗)`, required for every history of length `n`.

**Formalization Note** `mε ≥ 1` is encoded as `mε = n + 1` with `n : ℕ`. The paper's
"for all realizations of `P∗`" is stated for every history of length `n`; on histories of
probability zero `Pstar` can be redefined without changing properties 1 and 3, so this is the
paper's statement. `‖·‖₁` is `∑_k |·|`. -/
theorem lemma_5_3 {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (p1 : stdSimplex ℝ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (σε : List (A × S) → A) (Pstar : List (A × S) → stdSimplex ℝ K),
      1 - ε ≤ (lawOfPlays Γ p1 σε).real
        {ω | ∑ k, |(belief Γ p1 σε (historyAt n ω)).1 k - (Pstar (historyAt n ω)).1 k| ≤ ε} ∧
      (∀ h : List (A × S), h.length = n →
        ∃ σ : List (A × S) → A, IsErgodic Γ (Pstar h) σ ∧
          gammaInf Γ (Pstar h) σ = vInf Γ (Pstar h)) ∧
      vInf Γ p1 - ε ≤ ∫ ω, vInf Γ (Pstar (historyAt n ω)) ∂(lawOfPlays Γ p1 σε) := by sorry

end FiniteMemPOMDP
