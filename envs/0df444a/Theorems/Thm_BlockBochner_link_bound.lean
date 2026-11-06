-- Prove2me | Theorems.Thm_BlockBochner_link_bound
-- name    : BlockBochner.link_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:39:35.959184+00:00
-- url     : https://prove2.me/theorems/95d64532-00c8-4daa-a03a-ea3944d5c7b4
-- title:
--   Sec. 3.4, p.26 — link bound $\|L_iL_j-L_{ij}\|_{\mathrm{op}}\le a_{ij}$
-- statement:
--   Let $\mu$ be a probability measure on $\prod_{v\in V}S_v$, with $V$ finite and every $S_v$ standard Borel. Let $i\ne j$ be sites and $a\ge0$. Suppose that for almost every pinning $\tau$ of $V\setminus\{i,j\}$ (with respect to the law of $X_{V\setminus\{i,j\}}$) the two-site link satisfies
--   $$\lambda_2(L^\tau_{\mathrm{Glaub}})\ge\frac{1-a}2 .$$
--   Then, on $L^2(\mu)$,
--   $$\|L_iL_j-L_{ij}\|_{\mathrm{op}}\le a,$$
--   where $L_{ij}$ is the orthogonal projection onto $\operatorname{ran}L_i\cap\operatorname{ran}L_j$.
--
--   This is the step of the proof of Theorem 3 that turns the local hypothesis on links into the hypothesis of Theorem 21 for $H=L^2(\mu)$, $W_i=\operatorname{ran}L_i$, $s_{ij}=a_{ij}$.
--
--   Differences from the source:
--   - generalization: a = a_ij, an entry of an admissible matrix A, applied to every pair → one pair i ≠ j and any real a ≥ 0; reason: the argument uses only the hypothesis on this pair; a_ij ≥ 0, so the source's use is an instance
--   - encoding: all pinnings τ of V ∖ {i, j} → pinLaw µ {i, j}-a.e. τ, with µ^τ a regular conditional distribution (condDistrib); reason: the source states that all statements about pinnings hold a.e. w.r.t. the law of the pinned spins (Sec. 2.2, p.15)
--   - encoding: λ₂(L^τ_Glaub) ≥ (1 − a)/2 → GapAtLeast (glauberLap (linkLaw µ {i, j} τ)) ((1 − a)/2); reason: the Sec. 1.1 definition of λ₂
--   - generalization: the hypotheses of Theorem 3 in force (µ connected, A admissible) → neither assumed; reason: the bound is derived link by link from the hypothesis on the pinnings of V ∖ {i, j} alone; the source's instance (connected µ, admissible A) is a special case
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.4, p.26 (proof of Theorem 3)

import Mathlib
import Definitions.Def_BlockBochner_GapAtLeast
import Definitions.Def_BlockBochner_glauberLap
import Definitions.Def_BlockBochner_pinLaw
import Definitions.Def_BlockBochner_linkLaw
import Definitions.Def_BlockBochner_projCl

open MeasureTheory

namespace BlockBochner

/-- **The link bound in the proof of Theorem 3.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.4, p.26: "interpreting the local
assumption on links using Lemma 13 and averaging, we have `‖L_iL_j − L_{ij}‖_op ≤ a_{ij}`", where
`L_{ij}` is the orthogonal projection onto `ran L_i ∩ ran L_j` in `L²(µ)`.

Let `µ` be a probability measure on `∏_v S_v` (finitely many sites, standard Borel spins), `i ≠ j`
and `a ≥ 0`. If for almost every pinning `τ` of `V ∖ {i, j}` the two-site link has
`λ₂(L^τ_Glaub) ≥ (1 − a)/2`, then `‖L_i L_j − L_{ij}‖_op ≤ a` on `L²(µ)`.

**Formalization Note** Stated for one pair and one number `a ≥ 0` (the source uses `a = a_{ij}`).
`L_i = siteLap µ i`; `L_{ij}` projects onto the closure of `ran L_i ∩ ran L_j`, which is closed. -/
theorem link_bound {V : Type*} [Fintype V] [DecidableEq V] {S : V → Type*}
    [∀ v, MeasurableSpace (S v)] [∀ v, StandardBorelSpace (S v)] [∀ v, Nonempty (S v)]
    (μ : Measure (∀ v, S v)) [IsProbabilityMeasure μ] {i j : V} (hij : i ≠ j) {a : ℝ} (ha : 0 ≤ a)
    (hlink : ∀ᵐ τ ∂(pinLaw μ {i, j}), GapAtLeast (glauberLap (linkLaw μ {i, j} τ)) ((1 - a) / 2)) :
    ‖siteLap μ i ∘L siteLap μ j -
      projCl (LinearMap.range (siteLap μ i).toLinearMap ⊓
        LinearMap.range (siteLap μ j).toLinearMap)‖ ≤ a := by sorry

end BlockBochner
