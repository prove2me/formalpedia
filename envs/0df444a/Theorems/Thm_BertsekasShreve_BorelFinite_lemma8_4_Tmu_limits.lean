-- Prove2me | Theorems.Thm_BertsekasShreve_BorelFinite_lemma8_4_Tmu_limits
-- name    : BertsekasShreve.BorelFinite.lemma8_4_Tmu_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:18:06.158188+00:00
-- url     : https://prove2.me/theorems/59fbdb4d-17fe-4344-a387-0ffcf0733a34
-- title:
--   Lemma 8.4 — monotone and bounded convergence for the operator T_μ
-- statement:
--   Consider the finite horizon Borel model of Definition 8.1. Let $\{J_k\}$ be a sequence of extended real-valued, universally measurable functions on $S$, let $J:S\to R^*$, and let $\mu\in U(C\mid S)$.
--   1. If $T_\mu(J_1)(x)<\infty$ for every $x\in S$ and $J_k\downarrow J$, then $T_\mu(J_k)\downarrow T_\mu(J)$.
--   2. If $T_\mu(J_1^-)(x)<\infty$ for every $x\in S$, $g\ge0$, and $J_k\uparrow J$, then $T_\mu(J_k)\uparrow T_\mu(J)$.
--   3. If $\{J_k\}$ is uniformly bounded, $g$ is bounded, and $J_k\to J$, then $T_\mu(J_k)\to T_\mu(J)$.
--
--   Here $J_1^-=\max(-J_1,0)$, the arrows denote monotone pointwise convergence, and all limits are pointwise in $x$:
--   $$T_\mu(J_k)(x)\longrightarrow T_\mu(J)(x)\qquad\forall x\in S.$$
--
--   These continuity properties let infima over policies be exchanged with the operator $T_\mu$ in the dynamic programming recursion.
--
--   **Formalization Note** The sequence is indexed from $0$, so the book's $J_1$ is `Js 0`. The conditions $g\ge0$ and "$g$ bounded" are imposed on $\Gamma$, where $g$ is defined. "$\{J_k\}$ uniformly bounded" means $|J_k(x)|\le b$ for one real $b$, all $k$ and $x$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 197, Lemma 8.4

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Model
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_BorelFinite_Operators

namespace BertsekasShreve.BorelFinite

open Filter Topology in
/-- **Lemma 8.4** (p. 197). Let `{J_k}` be universally measurable functions `S → R*` and
`μ ∈ U(C|S)` (the book's `J₁` is `Js 0` here).
(a) If `T_μ(J₁)(x) < ∞` for every `x` and `J_k ↓ J`, then `T_μ(J_k) ↓ T_μ(J)`.
(b) If `T_μ(J₁⁻)(x) < ∞` for every `x`, `g ≥ 0`, and `J_k ↑ J`, then `T_μ(J_k) ↑ T_μ(J)`.
(c) If `{J_k}` is uniformly bounded, `g` is bounded, and `J_k → J`, then `T_μ(J_k) → T_μ(J)`. -/
theorem lemma8_4_Tmu_limits {S C W : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [Nonempty S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [Nonempty C]
    [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [Nonempty W]
    (M : Model S C W)
    (μ : UCS M) (Js : ℕ → S → EReal) (Jl : S → EReal) (hJs : ∀ k, UMeasurable (Js k)) :
    ((∀ x, Tmu M μ (Js 0) x < ⊤) → (∀ x, Antitone fun k => Js k x) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        (∀ x, Antitone fun k => Tmu M μ (Js k) x) ∧
          ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) ∧
    ((∀ x, Tmu M μ (fun y => ((negPart (Js 0) y : ENNReal) : EReal)) x < ⊤) →
        (∀ z ∈ M.Γ, 0 ≤ M.g z) → (∀ x, Monotone fun k => Js k x) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        (∀ x, Monotone fun k => Tmu M μ (Js k) x) ∧
          ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) ∧
    ((∃ b : ℝ, ∀ k x, Js k x ≤ b ∧ -(b : EReal) ≤ Js k x) →
        (∃ b : ℝ, ∀ z ∈ M.Γ, M.g z ≤ b ∧ -(b : EReal) ≤ M.g z) →
        (∀ x, Tendsto (fun k => Js k x) atTop (𝓝 (Jl x))) →
        ∀ x, Tendsto (fun k => Tmu M μ (Js k) x) atTop (𝓝 (Tmu M μ Jl x))) := by sorry

end BertsekasShreve.BorelFinite
