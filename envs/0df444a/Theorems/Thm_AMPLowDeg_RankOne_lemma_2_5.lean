-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_2_5
-- name    : AMPLowDeg.RankOne.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:05:35.974031+00:00
-- url     : https://prove2.me/theorems/0c456b81-dcd3-4e34-a41a-a87bc06cb7cb
-- title:
--   Lemma 2.5 — disconnected and non-tree parts
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, $n\ge1$, and take the auxiliary observation (2.9) with $s=q_{\mathrm{AMP}}$.
--
--   1. If $|\alpha|\ge1$ and either $1\notin V(\alpha)$ or $\alpha$ is disconnected, then $A_\alpha(\theta)=0$ almost surely.
--   2. Let $\mathcal J$ be the collection of nonempty connected $\alpha$ with $\tau(\alpha)\ge1$. Then for every $D$,
--   $$
--   \sum_{\substack{|\alpha|\le D,\ \alpha\in\mathcal J\\ 1\in V(\alpha)}}\frac{\mathbb E[A_\alpha(\theta)^2]}{n^{|\alpha|}\,\alpha!}\le\sum_{g=1}^{D}\left(\frac{2^{54}(D+1)^{48}M_D^{16}}{n}\right)^{g}.
--   $$
--
--   Together with Lemma 2.4 this splits the right-hand side of (2.11) into $q_{\mathrm{AMP}}$ plus a remainder that is small when $D^{48}M_D^{16}=o(n)$.
--
--   Differences from the source:
--
--   - encoding: A_α(θ) and C_γ(H) on the probability space of (θ, W, Z) → on the space of (θ, Z) with law π^{⊗n} ⊗ 𝒩(0, I_n) (chanLaw); R = √s θ + Z, H = sθ + √s Z; reason: W is independent of (θ, Z) and enters neither A_α nor C_γ(H), so the expectations are the same
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 8, Lemma 2.5 (1)–(2); proofs p. 14 and pp. 20–21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Potential
import Definitions.Def_AMPLowDeg_RankOne_Graph
import Definitions.Def_AMPLowDeg_RankOne_Aux

open MeasureTheory ProbabilityTheory
open Classical

namespace AMPLowDeg.RankOne

/-- Lemma 2.5, p. 8 — disconnected and non-tree parts, for the auxiliary observation (2.9)
(`s = q_AMP`): (1) if `|α| ≥ 1` and either `1 ∉ V(α)` or `α` is disconnected, then
`A_α(θ) = 0` almost surely; (2) with `𝒥` the nonempty connected `α` with `τ(α) ≥ 1`,
`Σ_{|α| ≤ D, α ∈ 𝒥, 1 ∈ V(α)} E[A_α(θ)²] / (n^{|α|} α!) ≤ Σ_{g=1}^{D} (2^{54}(D+1)^{48} M_D^{16} / n)^g`.
Vertex `1` is `⟨0, hn⟩`. -/
theorem lemma_2_5 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) (n : ℕ) (hn : 0 < n) :
    (∀ α : Edge n → ℕ, 1 ≤ absIdx α → ((⟨0, hn⟩ : Fin n) ∉ vertexSet α ∨ ¬ IsConnected α) →
      Aaux π (qAMP π) ⟨0, hn⟩ α =ᵐ[chanLaw π n] 0) ∧
    (∀ D : ℕ,
      ∑ α ∈ (multiIdx n D).filter (fun α => InJ α ∧ (⟨0, hn⟩ : Fin n) ∈ vertexSet α),
          (∫ w, (Aaux π (qAMP π) ⟨0, hn⟩ α w) ^ 2 ∂(chanLaw π n)) /
            ((n : ℝ) ^ absIdx α * (factIdx α : ℝ)) ≤
        ∑ g ∈ Finset.Icc 1 D, ((2 : ℝ) ^ 54 * ((D : ℝ) + 1) ^ 48 * MD π D ^ 16 / n) ^ g) := by sorry

end AMPLowDeg.RankOne
