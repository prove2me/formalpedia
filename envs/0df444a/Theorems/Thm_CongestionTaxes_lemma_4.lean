-- Prove2me | Theorems.Thm_CongestionTaxes_lemma_4
-- name    : CongestionTaxes.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:57.280098+00:00
-- url     : https://prove2.me/theorems/0deec685-da4d-475d-bacd-008335e6164e
-- title:
--   Lemma 4 — $p$ is well defined, convex and infinitely differentiable on $\mathbb R_{\ge0}$
-- statement:
--   Let $\ell:\mathbb N\to\mathbb R_{>0}$ satisfy Assumption 1, with $\ell(0)=0$, and let $\rho_\ell<\infty$. Let $p(v)=\mathbb E_{P\sim\mathrm{Poi}(v)}[P\ell(P)]=\bigl(\sum_{i\ge0}i\ell(i)v^i/i!\bigr)e^{-v}$. Then:
--
--   1. for every $v\ge0$ the series $\sum_{i\ge0}i\ell(i)v^i/i!$ converges;
--   2. $p(v)\ge0$ for every $v\ge0$;
--   3. $p$ is convex on $\mathbb R_{\ge0}$;
--   4. $p$ is infinitely differentiable on $\mathbb R_{\ge0}$.
--
--   Convexity of each $p_r$ makes the relaxation (12) a convex program, which is what makes the optimal taxes computable.
--
--   Differences from the source:
--
--   - generalization: Define $p:\mathbb R_{\ge0}\to\mathbb R_{\ge0}$ (statement); convergence shown in the proof (p.28) → clauses 1–2: summability of the series and $p(v)\ge0$ for all $v\ge0$; reason: a Lean `tsum` is $0$ on a divergent series, so the well-definedness the proof establishes is stated; dropping clauses 1–2 gives the printed lemma
--   - encoding: differentiable infinitely many times in $\mathbb R_{\ge0}$ → `ContDiffOn ℝ ∞` on $[0,\infty)$; reason: the same notion
--   - encoding: $\ell:\mathbb N\to\mathbb R_{>0}$ extended by $\ell(0)=0$ → $\ell:\mathbb N\to\mathbb R$ with $\ell(0)=0$ inside Assumption 1, $\rho_\ell$ in $[0,\infty]$; reason: the paper's own extension (p.5); same instances
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, Lemma 4, p.27, and its proof, p.28

import Mathlib
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_poissonValue
import Definitions.Def_CongestionTaxes_rho

open scoped ENNReal ContDiff

namespace CongestionTaxes

/-- **Lemma 4** (Paccagnan, Gairing, arXiv:2105.07480v2, Lemma 4, p.27, with the well-definedness
shown at the start of its proof, p.28). Let `ℓ` satisfy Assumption 1 with `ρ_ℓ < ∞`. Then:
1. for every `v ≥ 0` the series `∑_i i ℓ(i) vⁱ / i!` converges (so `p(v)` of (10) is well defined);
2. `p(v) ≥ 0` for every `v ≥ 0` (`p : ℝ≥0 → ℝ≥0`);
3. `p` is convex on `ℝ≥0`;
4. `p` is infinitely differentiable on `ℝ≥0`.

**Formalization Note** "Differentiable infinitely many times in `ℝ≥0`" is `ContDiffOn ℝ ∞` on
`Set.Ici 0`. -/
theorem lemma_4 (ℓ : ℕ → ℝ) (hℓ : Assumption1 ℓ) (hρ : rho ℓ < ⊤) :
    (∀ v : ℝ, 0 ≤ v → Summable (fun i : ℕ => (i : ℝ) * ℓ i * v ^ i / (i.factorial : ℝ))) ∧
    (∀ v : ℝ, 0 ≤ v → 0 ≤ poissonValue ℓ v) ∧
    ConvexOn ℝ (Set.Ici 0) (poissonValue ℓ) ∧
    ContDiffOn ℝ ∞ (poissonValue ℓ) (Set.Ici 0) := by sorry

end CongestionTaxes
