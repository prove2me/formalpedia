-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_2_4
-- name    : AMPLowDeg.RankOne.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:05:16.906202+00:00
-- url     : https://prove2.me/theorems/f2be6895-a9b6-4319-8503-52fd338dfeda
-- title:
--   Lemma 2.4 — rooted-tree part
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, $n\ge1$, $D\ge0$, and take the auxiliary observation (2.9), $R=\sqrt s\theta+Z$ with $s=q_{\mathrm{AMP}}$. Let $\mathcal T$ be the collection of nonempty connected $\alpha$ with $|\alpha|=|V(\alpha)|-1$. Then
--
--   $$
--   \mathbb E[A_0(\theta)^2]+\sum_{\substack{|\alpha|\le D,\ \alpha\in\mathcal T\\ 1\in V(\alpha)}}\frac{\mathbb E[A_\alpha(\theta)^2]}{n^{|\alpha|}\,\alpha!}\le q_{\mathrm{AMP}}.
--   $$
--
--   The tree part of (2.11) thus contributes at most the AMP overlap $q_{\mathrm{AMP}}$, which is exactly the term in the final bound $m_2-q_{\mathrm{AMP}}$.
--
--   Differences from the source:
--
--   - encoding: A_α(θ) and C_γ(H) on the probability space of (θ, W, Z) → on the space of (θ, Z) with law π^{⊗n} ⊗ 𝒩(0, I_n) (chanLaw); R = √s θ + Z, H = sθ + √s Z; reason: W is independent of (θ, Z) and enters neither A_α nor C_γ(H), so the expectations are the same
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 8, Lemma 2.4; proof pp. 11–14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Potential
import Definitions.Def_AMPLowDeg_RankOne_Graph
import Definitions.Def_AMPLowDeg_RankOne_Aux

open MeasureTheory ProbabilityTheory
open Classical

namespace AMPLowDeg.RankOne

/-- Lemma 2.4, p. 8 — rooted-tree part: for the auxiliary observation (2.9) (`s = q_AMP`),
`E[A₀(θ)²] + Σ_{|α| ≤ D, α ∈ 𝒯, 1 ∈ V(α)} E[A_α(θ)²] / (n^{|α|} α!) ≤ q_AMP`, where `𝒯` is the
set of nonempty connected `α` with `|α| = |V(α)| − 1`. Vertex `1` is `⟨0, hn⟩`. -/
theorem lemma_2_4 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) (n D : ℕ) (hn : 0 < n) :
    (∫ w, (Aaux π (qAMP π) ⟨0, hn⟩ 0 w) ^ 2 ∂(chanLaw π n)) +
      ∑ α ∈ (multiIdx n D).filter (fun α => InTrees α ∧ (⟨0, hn⟩ : Fin n) ∈ vertexSet α),
        (∫ w, (Aaux π (qAMP π) ⟨0, hn⟩ α w) ^ 2 ∂(chanLaw π n)) /
          ((n : ℝ) ^ absIdx α * (factIdx α : ℝ)) ≤ qAMP π := by sorry

end AMPLowDeg.RankOne
