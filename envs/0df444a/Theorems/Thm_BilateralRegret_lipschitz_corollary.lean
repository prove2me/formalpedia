-- Prove2me | Theorems.Thm_BilateralRegret_lipschitz_corollary
-- name    : BilateralRegret.lipschitz_corollary
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:02.291503+00:00
-- url     : https://prove2.me/theorems/02fa9609-4a1c-4d9d-8fbb-91fc3d6b0b81
-- title:
--   Corollary of Lemma 1 (§3) — bounded densities make $p\mapsto\mathbb E[\mathrm{GFT}(p,S,B)]$ $4M$-Lipschitz
-- statement:
--   Let $S$ and $B$ be $[0,1]$-valued random variables whose laws have densities bounded by $M$: $\mathbb P[S\in A]\le M\,\mathrm{Leb}(A)$ and $\mathbb P[B\in A]\le M\,\mathrm{Leb}(A)$ for every Borel set $A$. Then for all prices $p,q\in[0,1]$,
--
--   $$
--   \big|\mathbb E[\mathrm{GFT}(p,S,B)]-\mathbb E[\mathrm{GFT}(q,S,B)]\big|\le 4M\,|p-q| .
--   $$
--
--   No independence between $S$ and $B$ is assumed. Lipschitz continuity is what allows Scouting Bandits to restrict attention to a finite grid of prices.
--
--   Differences from the source:
--   - encoding: [0,1]-valued random variables S, B → measurable maps S, B on a probability space with S ω, B ω ∈ [0,1] for every ω; probabilities are real numbers (Measure.real); reason: Lean representation of random variables; same instances
--   - generalization: the valuations have densities bounded by M; (bd), p.6 and p.24: the joint density of (S₁, B₁) is bounded by M → each of μ_S, μ_B satisfies μ(A) ≤ M · Leb(A) for every Borel A; reason: a joint density f ≤ M on [0,1]² gives marginal densities ∫ f ≤ M, so every instance of the source is covered; the printed proof only uses the marginals (paper.md R1)
--   - reading: E[GFT(·, S, B)] is 4M-Lipschitz → |E GFT(p) − E GFT(q)| ≤ 4M|p − q| for all p, q ∈ [0,1]; reason: the expected gain from trade is a function of the price, whose domain is [0,1]
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, Bilateral Trade: A Regret Minimization Perspective, arXiv:2109.12974v1, Corollary of Lemma 1, §3, p.7 (proof p.21)

import Mathlib
import Definitions.Def_BilateralRegret_regret

namespace BilateralRegret

open MeasureTheory

/-- **Corollary of Lemma 1 (§3): bounded densities make the expected gain from trade
`4M`-Lipschitz.**
Cesa-Bianchi, Cesari, Colomboni, Fusco, Leonardi, *Bilateral Trade: A Regret Minimization
Perspective*, arXiv:2109.12974v1, §3, p.7 (proof p.21).

Let `S`, `B` be `[0,1]`-valued random variables whose laws each satisfy
`ℙ[S ∈ A] ≤ M · Leb(A)` and `ℙ[B ∈ A] ≤ M · Leb(A)` for every Borel set `A`. Then for all
`p, q ∈ [0,1]`, `|𝔼[GFT(p, S, B)] − 𝔼[GFT(q, S, B)]| ≤ 4M |p − q|`.

**Formalization Note.** The paper assumes that `(S, B)` has a joint density bounded by `M`; this
statement assumes only that each marginal has a density bounded by `M`, which a joint density
bounded by `M` on `[0,1]²` implies. No independence is assumed. -/
theorem lipschitz_corollary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S B : Ω → ℝ) (hSm : Measurable S) (hBm : Measurable B)
    (hS : ∀ ω, S ω ∈ Set.Icc (0 : ℝ) 1) (hB : ∀ ω, B ω ∈ Set.Icc (0 : ℝ) 1)
    (M : ℝ) (hMS : DensityBoundedBy M (P.map S)) (hMB : DensityBoundedBy M (P.map B)) :
    ∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      |∫ ω, GFT p (S ω) (B ω) ∂P - ∫ ω, GFT q (S ω) (B ω) ∂P| ≤ 4 * M * |p - q| := by sorry

end BilateralRegret
