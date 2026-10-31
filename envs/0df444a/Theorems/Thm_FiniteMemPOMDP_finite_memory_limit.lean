-- Prove2me | Theorems.Thm_FiniteMemPOMDP_finite_memory_limit
-- name    : FiniteMemPOMDP.finite_memory_limit
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:05.491159+00:00
-- url     : https://prove2.me/theorems/de3697f0-c69b-494c-b550-6c2cfda86171
-- title:
--   §6.4 — expected averages of a finite-memory strategy converge to $\gamma_\infty$
-- statement:
--   For every initial belief $p$ and every finite-memory strategy $\sigma$,
--
--   $$\lim_{n\to\infty}\mathbb E^{p}_{\sigma}\Big(\frac1n\sum_{m=1}^nG_m\Big)=\mathbb E^{p}_{\sigma}\Big(\liminf_{n\to+\infty}\frac1n\sum_{m=1}^nG_m\Big)=\gamma^{p}_\infty(\sigma).$$
--
--   The paper uses this for the block strategy $\sigma'$ along the subsequence $n=Ln_0$ to conclude Lemma 5.7 from Lemma 6.9.
--
--   Differences from the source:
--   - encoding: ∆(K), ∆(A) probability vectors; q: K × A → ∆(K × S); histories in ∪_m (A × S)^{m−1}; plays in (K × A × S)^ℕ; K, A, S finite → stdSimplex ℝ K / stdSimplex ℝ A; q as PMF (K × S); histories as chronological List (A × S); plays as ℕ → PlayStep A S K with coordinate n+1 = (A_{n+1}, S_{n+1}, K_{n+2}); K, A, S finite and nonempty; reason: Lean representations of the same objects; nonemptiness is implicit in the paper (p1 ∈ ∆(K), σ needs an action, q(k,a) ∈ ∆(K × S) needs a signal); the play space is a bijective re-indexing
--   - generalization: the block strategy σ′, initial belief p*, the subsequence n = L n0 → every finite-memory σ, every initial belief p, the full sequence n → ∞; reason: σ′ has finite memory and a subsequence of a convergent sequence has the same limit, so the statement gives the paper's display
--   - encoding: σ = (σu, σa, M, m0) with M a finite set → ∃ M : Type with Finite M, m0, σa, σu generating σ by a left fold over the history; reason: the standard transducer semantics, which the paper leaves implicit
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §6.4, p.20

import Mathlib
import Definitions.Def_FiniteMemPOMDP_gammaInf
import Definitions.Def_FiniteMemPOMDP_IsFiniteMemory

open MeasureTheory Filter Topology

namespace FiniteMemPOMDP

/-- **§6.4, final display — expected averages of a finite-memory strategy converge to `γ∞`.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §6.4, p.20: "To conclude, since σ′ has finite
memory, we have lim_{L→+∞} E^{p∗}_{σ′} ( (1/(Ln0)) ∑_{m=1}^{Ln0} Gm ) =
E^{p∗}_{σ′} ( lim inf_{n→+∞} (1/n) ∑_{m=1}^n Gm ) = γ^{p∗}_∞(σ′)".

For every initial belief `p` and every finite-memory strategy `σ`, the expected averages
`E^p_σ((1/n) ∑_{m=1}^n G_m)` converge, as `n → ∞`, to `γ^p_∞(σ)`.

**Formalization Note** The paper states this for the block strategy `σ′`, its initial belief
`p∗` and the subsequence `n = L n0`; the statement here is for every finite-memory strategy, every
initial belief and the full sequence, and gives the paper's display by passing to the
subsequence `L n0`. -/
theorem finite_memory_limit {K A S : Type} [Fintype K] [DecidableEq K] [Nonempty K] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype S] [DecidableEq S] [Nonempty S]
    (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A) (hσ : IsFiniteMemory σ) :
    Tendsto (fun n : ℕ => ∫ ω, avgReward Γ n ω ∂(lawOfPlays Γ p σ)) atTop
      (𝓝 (gammaInf Γ p σ)) := by sorry

end FiniteMemPOMDP
