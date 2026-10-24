-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_lemma_9_ii
-- name    : APrioriTSP.Sampling.lemma_9_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:36.195011+00:00
-- url     : https://prove2.me/theorems/e3101c69-3b25-4ca7-8096-3fe6de4030e8
-- title:
--   Lemma 9 (ii), p. 6 — an upper bound on (2) for f(p) = σp on ε_i-normalized instances is one for f(p) = 1 − (1 − p)^σ on all instances with depot
-- statement:
--   Let $\alpha \ge 0$ and $\sigma \in (0,1)$, and let $(\varepsilon_i)_{i\in\mathbb N}$ be a sequence in $(0,1]$ with $\lim_{i\to\infty}\varepsilon_i = 0$. Let $\mathcal I$ be the class of all $\varepsilon$-normalized instances with $\varepsilon = \varepsilon_i$ for some $i$. Let $\rho \in \mathbb R$, and suppose that on every instance $(V, c, p) \in \mathcal I$,
--   $$\mathbb E_{S\sim f\circ p}\Big[\alpha\cdot\mathrm{OPT}_{\mathrm{TSP}}(S,c) + 2\sum_{v\in V}p(v)\,c(v,S)\Big] \le \rho\cdot\mathrm{OPT}\qquad\text{for } f(x) = \sigma x\ (x < 1),\ f(1) = 1 .$$
--   Then the same bound holds on every instance of the a priori TSP with a depot for $f(x) = 1 - (1-x)^\sigma$.
--
--   The reduction lets §2 study only instances in which all customers except the depot have the same tiny activation probability; it is the last step from (Sampling-LP) to arbitrary instances.
--
--   **Formalization Note** Both the hypothesis and the conclusion quantify over all finite customer types, semi-metrics and activation probabilities.
--
--   Differences from the source:
--
--   - generalization: α ≥ 1, the approximation guarantee of the TSP algorithm of step (ii) (p. 4) → every real α ≥ 0; reason: (2) is a formula in α and the argument uses only α ≥ 0; at every α ≥ 1 the Lean statement is the paper's
--   - generalization: an upper bound ρ on the ratio (2) with 0/0 := 1 (so ρ ≥ 1: an instance with OPT = 0 has ratio 1) → every real ρ, with (2) ≤ ρ written as E_{S∼f∘p}[…] ≤ ρ·OPT; reason: for ρ ≥ 1 the multiplicative form is the paper's bound (if OPT = 0 both sides are 0); for ρ < 1 the hypothesis already fails, since on V = {d, a} with c(d, a) = 1 and p(a) = ε_i the ratio is ασ + 1 − σε_i, and its infimum over i is at least 1 since ε_i → 0, so the implication only gains vacuous cases
--   - encoding: f(p) = σp for all p ∈ (0, 1) → f(x) = σx for x ≠ 1 and f(1) = 1; reason: the algorithm requires f(1) = 1 (p. 4) and the proof sets f′(1) := 1 (p. 34); values off (0, 1] never enter
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 6, Lemma 9 (ii) (proof §7, pp. 34–36)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

namespace APrioriTSP.Sampling

/-- Lemma 9 (ii) (p. 6): an upper bound on (2) for `f(p) = σ p` over all `ε_i`-normalized
instances (`ε_i → 0`) is an upper bound on (2) for `f(p) = 1 − (1 − p)^σ` over all instances with
a depot. -/
theorem lemma_9_ii (α σ : ℝ) (hα : 0 ≤ α) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i ∧ ε i ≤ 1)
    (hlim : Filter.Tendsto ε Filter.atTop (nhds 0)) (ρ : ℝ) :
    (∀ (i : ℕ) (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
        IsNormalized c p d (ε i) → samplingCost α (linSampling σ) c p ≤ ρ * aPrioriOpt c p) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
        IsDepotInstance c p d → samplingCost α (powerSampling σ) c p ≤ ρ * aPrioriOpt c p := by sorry

end APrioriTSP.Sampling
