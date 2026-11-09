-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_6_1
-- name    : AMPLowDeg.RankOne.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:05:26.901536+00:00
-- url     : https://prove2.me/theorems/56f0cb16-e3a7-465e-a31d-94ad00baf559
-- title:
--   Lemma 6.1 — reduction to rooted cores (6.1)
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, $n\ge1$, $D\ge0$, take the channel (2.9) with $s=q_{\mathrm{AMP}}$ and the field $H$ of (4.2). Then
--
--   $$
--   \sum_{\substack{0<|\alpha|\le D\\ \alpha\in\mathcal J,\ 1\in V(\alpha)}}\frac{\mathbb E[A_\alpha(\theta)^2]}{n^{|\alpha|}\,\alpha!}\ \le\ \sum_{\substack{\gamma\text{ rooted core}\\ 1\le|\gamma|\le D}}\frac{n^{-\tau(\gamma)}}{\mathrm{Aut}(\gamma)\,\gamma!}\,\mathbb E\big[C_\gamma(H)^2\big],
--   $$
--
--   where the sum over rooted cores contains one representative of each rooted isomorphism class with at most $n$ vertices, and $\mathrm{Aut}(\gamma)$ is the number of vertex automorphisms of $\gamma$ that fix the root and preserve all edge multiplicities, loop multiplicities included.
--
--   The lemma removes the trees hanging off each graph, so the non-tree part of (2.11) is controlled by core cumulants alone.
--
--   **Formalization Note** The sum over isomorphism classes is written as a sum over all labelled rooted cores on $\{1,\dots,n\}$ with root $1$, each weighted by $1/\#\{\text{labelled copies of its class}\}$; every class with at most $n$ vertices has that many labelled representatives, and all of them have the same weight.
--
--   Differences from the source:
--
--   - encoding: sum over one representative of each rooted isomorphism class with at most n vertices → sum over all labelled rooted cores γ on Fin n with root 1, weighted by 1/numCopies(γ); reason: each class with at most n vertices has numCopies labelled representatives with the same Aut, γ!, τ and E[C_γ(H)²]; the two sums are equal
--   - encoding: A_α(θ) and C_γ(H) on the probability space of (θ, W, Z) → on the space of (θ, Z) with law π^{⊗n} ⊗ 𝒩(0, I_n) (chanLaw); R = √s θ + Z, H = sθ + √s Z; reason: W is independent of (θ, Z) and enters neither A_α nor C_γ(H), so the expectations are the same
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 14, Lemma 6.1, eq. (6.1); proof pp. 14–17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Potential
import Definitions.Def_AMPLowDeg_RankOne_Graph
import Definitions.Def_AMPLowDeg_RankOne_Aux

open MeasureTheory ProbabilityTheory
open Classical

namespace AMPLowDeg.RankOne

/-- Lemma 6.1, p. 14 — reduction to rooted cores (6.1): for the auxiliary observation (2.9)
(`s = q_AMP`, `H = sθ + √s Z`) and every `n, D`,
`Σ_{0<|α|≤D, α ∈ 𝒥, 1 ∈ V(α)} E[A_α(θ)²] / (n^{|α|} α!)
  ≤ Σ_{γ rooted core, 1 ≤ |γ| ≤ D} n^{−τ(γ)} / (Aut(γ) γ!) · E[C_γ(H)²]`,
the right sum taking one representative of each rooted isomorphism class with at most `n`
vertices. Here it is written as a sum over all labelled rooted cores on `Fin n` with root `1`,
each weighted by `1 / #(labelled copies of its class)`. Vertex `1` is `⟨0, hn⟩`. -/
theorem lemma_6_1 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) (n D : ℕ) (hn : 0 < n) :
    ∑ α ∈ (multiIdx n D).filter
        (fun α => 0 < absIdx α ∧ InJ α ∧ (⟨0, hn⟩ : Fin n) ∈ vertexSet α),
        (∫ w, (Aaux π (qAMP π) ⟨0, hn⟩ α w) ^ 2 ∂(chanLaw π n)) /
          ((n : ℝ) ^ absIdx α * (factIdx α : ℝ)) ≤
      ∑ γ ∈ (multiIdx n D).filter (fun γ => IsRootedCore ⟨0, hn⟩ γ ∧ 1 ≤ absIdx γ),
        (1 / (numCopies ⟨0, hn⟩ γ : ℝ)) *
          ((n : ℝ) ^ (-excess γ) / ((rootedAut ⟨0, hn⟩ γ : ℝ) * (factIdx γ : ℝ))) *
          ∫ w, (Ccum π (qAMP π) ⟨0, hn⟩ γ (Hfield (qAMP π) w)) ^ 2 ∂(chanLaw π n) := by sorry

end AMPLowDeg.RankOne
