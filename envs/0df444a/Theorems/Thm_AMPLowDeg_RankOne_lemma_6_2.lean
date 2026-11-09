-- Prove2me | Theorems.Thm_AMPLowDeg_RankOne_lemma_6_2
-- name    : AMPLowDeg.RankOne.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:06:46.282325+00:00
-- url     : https://prove2.me/theorems/d4972fa7-6680-41b3-afdf-cb2d118015fb
-- title:
--   Lemma 6.2 — cumulant expansion of a core (6.5), (6.6)
-- statement:
--   Let $\pi$ be a prior with $\mathbb E[\Theta]\ne0$ and all moments finite, $n\ge1$, $s>0$, $\eta=\eta_s$, $h\in\mathbb R^n$, and let $\theta_i\sim\pi_{s,h_i}$ independently.
--
--   1. For every $i$ and $m\ge1$, the cumulant of $m$ occurrences of $\theta_i$ is
--   $$
--   \mathrm{Cum}(\underbrace{\theta_i,\dots,\theta_i}_{m\text{ copies}})=\frac{d^m}{dz^m}\log\frac{Z_s(h_i+z)}{Z_s(h_i)}\Big|_{z=0}=\eta^{(m-1)}(h_i).
--   $$
--   2. For every rooted core $\gamma$ (root $1$), with the tagged occurrence sets $\mathcal I_i$ of p. 17,
--   $$
--   C_\gamma(h)=\sum_{\substack{\pi_i\in\Pi(\mathcal I_i),\ i\in V(\gamma)\\ \pi\text{ connected}}}\ \prod_{i\in V(\gamma)}\prod_{A\in\pi_i}\eta^{(|A|-1)}(h_i).
--   $$
--
--   The expansion writes a core cumulant as a sum of products of derivatives of the posterior mean, one factor per block; Lemma 6.3 bounds it term by term.
--
--   Differences from the source:
--
--   - reading: for every core γ → for every rooted core γ with root 1; reason: ℐ₁ contains the extra occurrence of θ₁, so the statement presupposes 1 ∈ V(γ); the cores of §6 are the rooted cores
--   - encoding: families π = (π_i)_{i ∈ V(γ)} with π_i ∈ Π(ℐ_i), π connected → partitions P of all tags whose blocks each lie in one ℐ_i (IsVertexHomog), connected when every tag is reachable from the extra θ₁ through blocks and edge copies (IsPartConnected); the product is over i and the blocks of P inside ℐ_i; reason: π_i is the set of blocks of P inside ℐ_i; this is a bijection, and reachability of tags is connectivity of the block multigraph
--   - encoding: θ_i ∼ π_{s,h_i} independently → the cumulant of the coordinate map θ ↦ θ_i under the product measure ⊗_j π_{s,h_j}; reason: same law
--   - encoding: vertex 1 of [n] → the vertex ⟨0, hn⟩ : Fin n, with the hypothesis 0 < n (vertices are 0-based); reason: the paper's vertex 1 exists only for n ≥ 1; relabelling changes no instance
--   - encoding: E|Θ|^p < ∞ for every real p ≥ 1 (standing assumption, p. 3) → AllMomentsFinite π: |x|^p is π-integrable for every natural p; reason: on a probability space finiteness for all integer p is equivalent to finiteness for all real p ≥ 1
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 18, Lemma 6.2, eqs. (6.5), (6.6); notation p. 17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model
import Definitions.Def_AMPLowDeg_RankOne_Cumulant
import Definitions.Def_AMPLowDeg_RankOne_Potential
import Definitions.Def_AMPLowDeg_RankOne_Graph
import Definitions.Def_AMPLowDeg_RankOne_Aux

open MeasureTheory ProbabilityTheory
open Classical

namespace AMPLowDeg.RankOne

/-- Lemma 6.2, p. 18 — cumulant expansion of a core: with `θᵢ ∼ π_{s,hᵢ}` independently, `s > 0`,
`η = η_s`: (6.5) for every `m ≥ 1`,
`Cum(θᵢ, …, θᵢ) [m copies] = d^m/dz^m log(Z_s(hᵢ + z)/Z_s(hᵢ))|_{z=0} = η^{(m−1)}(hᵢ)`;
(6.6) for every rooted core `γ`,
`C_γ(h) = Σ_{πᵢ ∈ Π(ℐᵢ), i ∈ V(γ), π connected} Π_{i ∈ V(γ)} Π_{A ∈ πᵢ} η^{(|A|−1)}(hᵢ)`.
A family `(πᵢ)` is encoded as one partition of all tags whose blocks each lie in a single `ℐᵢ`.
Vertex `1` is `⟨0, hn⟩`. -/
theorem lemma_6_2 (π : Measure ℝ) [IsProbabilityMeasure π] (hmean : mean π ≠ 0)
    (hmom : AllMomentsFinite π) (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 0 < s) (h : Fin n → ℝ) :
    (∀ (i : Fin n) (m : ℕ), 1 ≤ m →
      cum (Measure.pi fun j : Fin n => post π s (h j)) (fun _ : Fin m => fun θ : Fin n → ℝ => θ i) =
          iteratedDeriv m (fun z : ℝ => Real.log (Zpart π s (h i + z) / Zpart π s (h i))) 0 ∧
      iteratedDeriv m (fun z : ℝ => Real.log (Zpart π s (h i + z) / Zpart π s (h i))) 0 =
          iteratedDeriv (m - 1) (eta π s) (h i)) ∧
    (∀ γ : Edge n → ℕ, IsRootedCore ⟨0, hn⟩ γ →
      Ccum π s ⟨0, hn⟩ γ h =
        ∑ P ∈ (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Tag γ)))).filter
            (fun P => IsVertexHomog ⟨0, hn⟩ P ∧ IsPartConnected P),
          ∏ i : Fin n, ∏ A ∈ P.parts.filter (fun A => A ⊆ tagSet ⟨0, hn⟩ γ i),
            iteratedDeriv (A.card - 1) (eta π s) (h i)) := by sorry

end AMPLowDeg.RankOne
