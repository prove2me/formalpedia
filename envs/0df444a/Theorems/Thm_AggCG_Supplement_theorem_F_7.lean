-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_F_7
-- name    : AggCG.Supplement.theorem_F_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:31:21.926577+00:00
-- url     : https://prove2.me/theorems/4ed9ce7c-b4ac-4cd6-9b30-c1cbaffd5cc8
-- title:
--   Theorem F.7 — constructive self-simulation
-- statement:
--   Let $R_a:B_a\to[0,1]$ be the two increasing renormalizations of a state template, $h_a=R_a^{-1}$, and suppose $|h_a(u)-h_a(v)|\ge\kappa|u-v|$ for some $0<\kappa<1$. Every word $b\in\{0,1\}^T$ is realized by
--
--   $$
--   \theta_b=h_{b_1}\circ\cdots\circ h_{b_T}(1/2),
--   $$
--
--   and every parameter within $\kappa^T/4$ of this witness realizes the same word. Any evaluation probes satisfying the Lemma F.1 signal, interference, and error hypotheses therefore fat-shatter $T$ instances at the lemma's margin.
--
--   Differences from the source:
--   - encoding: the source carries controller states $q$, intervals $J_q$, and coordinates $\nu_q$ → Lean stores the normalized coordinate and its branch update directly; reason: the transition does not read $\theta$, so the normalized-coordinate recursion is equivalent to the stated template
--   - generalization: the source calls the evaluation instances valid → Lean requires only the explicit Lemma F.1 decomposition and bounds; reason: every valid source instance satisfying those bounds is included, and validity has no further role in the conclusion
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem F.7, p.40, PDF p.41; Definition F.6, p.39, PDF p.40

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_AggCG_Supplement_templateState

namespace AggCG.Supplement

open BartlettNN.Margin

/-- **Theorem F.7** (Constructive self-simulation; Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), p.40, PDF p.41), on the renormalizable state template of Definition F.6
(p.39): split `τ ∈ (0, 1)`, branches `B_0 = [0, τ]`, `B_1 = [τ, 1]`, increasing bijections
`R_a : B_a → [0, 1]` with inverses `h_a = R_a^{−1}` obeying `|h_a(u) − h_a(v)| ≥ κ|u − v|` for a fixed
`0 < κ < 1`. At depth `T`:
(1) every `b ∈ {0,1}^T` is realized (off the boundary) by `θ_b = h_{b_1} ∘ ⋯ ∘ h_{b_T}(1/2)`;
(2) every `θ` with `|θ − θ_b| ≤ κ^T/4` realizes `b` too (a stable neighbourhood of radius `κ^T/4`);
(3) if evaluation instances `x_1, …, x_T` obey Lemma F.1 (the criterion of Lemma A.4) at the witnesses
`θ_b`, the performance class `{f_θ : θ ∈ [0, 1]}` fat-shatters them at every margin
`0 < γ ≤ ½ min_i(Δ_i − ω_i − 2ε_i)`.

**Formalization Note** The template's states are represented by their normalized coordinate
(`templateState`). The word "valid" for the instances carries no formal content and is not assumed. -/
theorem theorem_F_7 (τ κ : ℝ) (R h : Bool → ℝ → ℝ) (hτ : 0 < τ ∧ τ < 1) (hκ : 0 < κ ∧ κ < 1)
    (hB : ∀ a : Bool, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      h a u ∈ (if a then Set.Icc τ 1 else Set.Icc 0 τ) ∧ R a (h a u) = u)
    (hR : ∀ a : Bool, ∀ v ∈ (if a then Set.Icc τ 1 else Set.Icc 0 τ), R a v ∈ Set.Icc (0 : ℝ) 1 ∧ h a (R a v) = v)
    (hmono : ∀ a : Bool, StrictMonoOn (R a) (if a then Set.Icc τ 1 else Set.Icc 0 τ))
    (hlip : ∀ a : Bool, ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1, κ * |u - v| ≤ |h a u - h a v|)
    (T : ℕ) :
    (∀ b : Fin T → Bool, TemplateRealizes τ R (templateWitness h b) b) ∧
    (∀ b : Fin T → Bool, ∀ θ : ℝ, |θ - templateWitness h b| ≤ κ ^ T / 4 → TemplateRealizes τ R θ b) ∧
    (∀ {X : Type} (f : ℝ → X → ℝ) (x : Fin T → X) (a Δ ω ε : Fin T → ℝ)
      (hfun e : Fin T → (Fin T → Bool) → ℝ),
      (∀ b i, f (templateWitness h b) (x i) = a i + Δ i * (if b i then 1 else 0) + hfun i b + e i b) →
      (∀ i b b', (∀ j, j ≠ i → b j = b' j) → hfun i b = hfun i b') →
      (∀ i b b', hfun i b - hfun i b' ≤ ω i) → (∀ i b, |e i b| ≤ ε i) →
      (∀ i, ω i + 2 * ε i < Δ i) → ∀ γ : ℝ, 0 < γ → (∀ i, γ ≤ (Δ i - ω i - 2 * ε i) / 2) →
        GammaShatters {g : X → ℝ | ∃ θ ∈ Set.Icc (0 : ℝ) 1, g = f θ} γ x) := by sorry

end AggCG.Supplement
