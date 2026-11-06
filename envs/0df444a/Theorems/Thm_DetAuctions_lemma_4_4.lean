-- Prove2me | Theorems.Thm_DetAuctions_lemma_4_4
-- name    : DetAuctions.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:08.738476+00:00
-- url     : https://prove2.me/theorems/0d813bfc-ba1c-4202-b5d0-04b1e0aabde0
-- title:
--   Lemma 4.4 — $\mathsf{REV}\le\mathsf{SREV}+\int_0^\infty\phi(\sum_j\bar F_j^{c_j})$ and the linear bound on $\phi$
-- statement:
--   Let $X_1,\dots,X_m$ be independent nonnegative random variables and caps $c_j\ge0$ chosen such that $\mathbb E[X_j\wedge c_j]=r_j=\mathsf{REV}(X_j)$ for every $j$. Let $\phi(x)=x-1+e^{-x}$. Then:
--   1. $\phi$ is nonnegative, nondecreasing and convex on $[0,\infty)$;
--   2. $$\mathsf{REV}(X)\le\mathsf{SREV}(X)+\int_0^\infty\phi\Big(\sum_{j=1}^m\bar F_j^{c_j}(t)\Big)\,dt;$$
--   3. $\phi(x)\le wx+(\phi(U)-wU)_+$ for arbitrary $w,U\ge0$ and $x\in[0,U]$.
--
--   Item 2 is the starting point of the constant-factor bounds of §4 (Propositions 4.6, 4.8, 4.10); item 3 linearizes $\phi$ on a bounded range.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. The laws are arbitrary independent laws on $[0,\infty)$, as printed.
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
--   - encoding: independent X_j ∼ F_j, real revenues → product law Measure.pi ν of probability laws ν j on ℝ≥0; revenues in ℝ≥0∞; reason: same instances; an unbounded law may have revenue +∞, where the inequalities read in [0, ∞]
--   - encoding: caps c_j with E[X_j ∧ c_j] = r_j → c j : ℝ≥0 with ∫⁻ min x (c j) ∂(ν j) = Rev1 (ν j) in ℝ≥0∞; reason: the same condition; caps are nonnegative as values are
--   - encoding: ∫ over (0, ∞) (or (c_j, ∞)) of a nonnegative integrand → lower integral of ENNReal.ofReal of the integrand over Set.Ioi, in ℝ≥0∞; reason: the integrands are nonnegative, so ofReal loses nothing and the value +∞ is kept
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Lemma 4.4, Eq. (26)–(28), pp.18–19 (pdf pp.20–21)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_DetAuctions_tail
import Definitions.Def_DetAuctions_phi

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Lemma 4.4**: for independent `X₁, …, X_m` and caps `cⱼ` with `E[Xⱼ ∧ cⱼ] = rⱼ = REV(Xⱼ)` for every
`j`, the function `φ(x) = x − 1 + e^{−x}` (26) is nonnegative, monotone and convex for `x ≥ 0`,
`REV(X) ≤ SREV(X) + ∫₀^∞ φ(Σⱼ F̄ⱼ^{cⱼ}(t)) dt` (27), and
`φ(x) ≤ wx + (φ(U) − wU)₊` for arbitrary `w, U ≥ 0` and `x ∈ [0, U]` (28).

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Lemma 4.4, Eq. (26)–(28), pp.18–19.

**Formalization Note** The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`.
The caps hypothesis is `∫ min{x, cⱼ} dνⱼ = Rev1 (ν j)` in `ℝ≥0∞`. The values are arbitrary
independent laws on `ℝ≥0`, as printed (not grid laws). `F̄ⱼ^{cⱼ}(t) = Prob[Xⱼ > cⱼ + t]` is
`tail (ν j) (cⱼ + t)`; the integral over `(0, ∞)` of the nonnegative `φ(·)` at a nonnegative
argument is a lower integral of `ENNReal.ofReal`. "Monotone" is nondecreasing on `[0, ∞)`. -/
theorem lemma_4_4 {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ≥0)
    [∀ j, IsProbabilityMeasure (ν j)] (c : ι → ℝ≥0)
    (hc : ∀ j, ∫⁻ x, ((min x (c j) : ℝ≥0) : ℝ≥0∞) ∂(ν j) = Rev1 (ν j)) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ phi x) ∧ MonotoneOn phi (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) phi ∧
    Rev (Measure.pi ν) ≤ SRev (Measure.pi ν) +
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (phi (∑ j, (tail (ν j) ((c j : ℝ) + t)).toReal)) ∧
    ∀ w U x : ℝ, 0 ≤ w → 0 ≤ U → x ∈ Set.Icc 0 U →
      phi x ≤ w * x + max (phi U - w * U) 0 := by sorry

end DetAuctions
