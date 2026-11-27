-- Prove2me | Theorems.Thm_DynChoiceJEO_Supplement_theorem_4
-- name    : DynChoiceJEO.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:14:15.512053+00:00
-- url     : https://prove2.me/theorems/ac1bbe62-ac98-49f5-9484-f08bc81f5bfe
-- title:
--   Theorem 4 (corrected: $\nabla\omega$ is the directional derivative) — online mirror descent has weighted regret $\le 2G^2/(\alpha(T+1))$
-- statement:
--   Let $E$ be a finite-dimensional real normed space with an arbitrary norm $\|\cdot\|$, let $\langle g,v\rangle$ be the value of a linear functional $g$ at $v$, and let $\|g\|_*=\sup\{\langle g,v\rangle:\|v\|\le1\}$ be the dual norm. A **subgradient on $Z\subseteq E$** of $f$ at $z\in Z$ is a functional $g$ with $f(u)\ge f(z)+\langle g,u-z\rangle$ for all $u\in Z$.
--
--   Let $Z\subseteq E$ be convex and $\omega:Z\to\mathbb R$ convex, with a selection $\nabla\omega$ that represents its one-sided derivatives along $Z$, that is, $\lim_{s\to0^+}[\omega(z+s(u-z))-\omega(z)]/s=\langle\nabla\omega(z),u-z\rangle$ for $z,u\in Z$, and with $\langle\nabla\omega(z)-\nabla\omega(z'),z-z'\rangle\ge\|z-z'\|^2$ on $Z$ (Assumption 3(a)).
--
--   Let $T\ge1$ and $\alpha>0$. For $t\in[T]$ let $h_t-\alpha\omega$ be convex on $Z$ (Assumption 4) and let $\nabla h_t(z)$ be a subgradient of $h_t$ on $Z$ at every $z\in Z$ with $\|\nabla h_t(z)\|_*\le G$ (Assumption 2). Let $\theta_t=t$, so $\Theta_T=\sum_{t\in[T]}t$, and let
--
--   $$
--   z_1\in\arg\min_{z\in Z}\omega(z),\qquad z_{t+1}\in\arg\min_{z\in Z}\Big\{\Big\langle\frac{2}{\alpha(t+1)}\nabla h_t(z_t)-\nabla\omega(z_t),z\Big\rangle+\omega(z)\Big\}\quad(1\le t<T).
--   $$
--
--   Then
--
--   $$
--   \frac1{\Theta_T}\sum_{t\in[T]}t\,h_t(z_t)-\min_{z\in Z}\frac1{\Theta_T}\sum_{t\in[T]}t\,h_t(z)\le\frac{2G^2}{\alpha(T+1)} .
--   $$
--
--   Relative strong convexity improves the $O(1/\sqrt T)$ regret of online mirror descent to $O(1/T)$ without a bound on the range of $\omega$.
--
--   The paper allows $\nabla\omega$ to be any subgradient selection, and the statement is then false: on $Z=[-1,1]$ with $\omega(z)=z^2/2+|z|$, $\nabla\omega(0)=-1$, $\alpha=1$, $h_t(z)=\omega(z)-2z$, $\nabla h_t(0)=-1$, $G=4$ and $T=64$, every iterate is $0$ and the regret $1/2$ exceeds $32/65$.
--
--   **Formalization Note** Functions on $Z$ are total functions on $E$ of which only the values on $Z$ are used. Each argmin means membership in $Z$ together with minimality on $Z$; existence and uniqueness are not assumed, and only $z_1,\dots,z_T$ are constrained. The regret bound is stated against every comparator in $Z$, which is the same bound on the weighted regret (14). The losses are arbitrary and may depend on the iterates.
--
--   Differences from the source:
--
--   - correction: ∇ω(z) is the gradient where ω is differentiable and otherwise any subgradient (p.6) → ∇ω represents the one-sided derivatives of ω along Z (IsDirectionalGradientOn), which implies the subgradient property for convex ω; reason: false as printed: Z = [−1,1], ω = z²/2 + |z|, ∇ω(0) = −1, ∇ω(z) = z + sgn z otherwise, α = 1, h_t = ω − 2z, ∇h_t(0) = −1, G = 4, T = 64 gives regret 1/2 > 32/65. Excluded cases: a kinked ω whose selection is not this derivative; every gradient of a differentiable ω is covered
--   - encoding: Euclidean space containing Z with some norm ∥·∥, inner product ⟨·,·⟩ → finite-dimensional real normed space E; gradients are continuous linear functionals and ⟨g,v⟩ is g v; reason: a linear functional is the same as a vector paired by the inner product; same instances
--   - correction: dual norm ∥x∥∗ := min_y{⟨x,y⟩ : ∥x∥ ≤ 1} (p.6) → the operator norm, max_y{⟨x,y⟩ : ∥y∥ ≤ 1}; reason: misprint: as printed y is unconstrained, so for x ≠ 0 with ∥x∥ ≤ 1 the minimum is −∞ and is not a norm
--   - encoding: functions ω, h_t : Z → ℝ, Z convex → total functions on E used only on Z; convexity of Z is part of ConvexOn ℝ Z ω; reason: every function on Z extends arbitrarily; same instances
--   - encoding: a subgradient of a function defined on Z → the inequality f(u) ≥ f(z) + g(u − z) for all u ∈ Z; reason: the subgradient of a function with domain Z; same instances
--   - encoding: weighted regret (14), with min over z ∈ Z, at most B → weightedRegretAgainst at most B for every u ∈ Z; reason: equivalent, and free of junk values of a real infimum
--   - encoding: argmin, with z_{t+1} written as equal to it → membership in Z and IsMinOn, for z_1,…,z_T only; reason: same runs: the objective is strictly convex under Assumption 3(a), so a minimizer is unique, and z_{T+1} does not enter the claim
--   - encoding: convex losses h_t (§4.2) → only h_t − αω convex, with ω convex and α > 0; reason: convexity of h_t follows from these; same instances
--   - encoding: horizon T ∈ ℕ with divisor Θ_T → hypothesis 1 ≤ T; reason: excludes only T = 0, where the averages are undefined
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, Theorem 4, p.15; Assumptions 2, 3(a) and 4, p.15; eq. (14), p.15; Notation, p.6; proof, p.ec2 (PDF 24)

import Mathlib
import Definitions.Def_ModernOnlineLearning_OMD_Defs
import Definitions.Def_DynChoiceJEO_Supplement_weightedRegretAgainst
import Definitions.Def_DynChoiceJEO_Supplement_IsDirectionalGradientOn

namespace DynChoiceJEO.Supplement

/-- **Theorem 4 (corrected: `∇ω` is the directional derivative of `ω` along `Z`): online mirror
descent under relative strong convexity.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*,
arXiv:1702.05702v5, Theorem 4, p.15: "Suppose that Z satisfies Assumption 3(a), and that for all t ∈ [T],
Assumptions 2 and 4 hold for h_t. Let θ_t = t for all t ∈ [T], and compute
z_1 ∈ arg min_{z∈Z} ω(z), z_{t+1} = arg min_{z∈Z} {⟨(2/(α(θ_t + 1)))∇h_t(z_t) − ∇ω(z_t), z⟩ + ω(z)}.
Then (1/Θ_T) ∑ θ_t h_t(z_t) − min_{z∈Z} (1/Θ_T) ∑ θ_t h_t(z) ≤ 2G²/(α(T+1))."
Assumption 2, p.15: "There exists a G < ∞ such that for any z ∈ Z, ‖∇h(z)‖_* ≤ G."
Assumption 3, p.15: "There exists a convex function ω : Z → ℝ satisfying: (a) for any z,z′ ∈ Z,
⟨∇ω(z) − ∇ω(z′), z − z′⟩ ≥ ‖z − z′‖²."
Assumption 4, p.15: "Let ω : Z → ℝ be a function satisfying Assumption 3(a). There exists α > 0
such that the function h − αω is convex."

**Correction** The paper lets `∇ω(z)` be any subgradient (p.6). The statement is then false:
on `Z = [-1,1]` take `ω(z) = z²/2 + |z|`, `∇ω(0) = -1`, `α = 1`, `h_t(z) = ω(z) - 2z`,
`∇h_t(0) = -1`, `G = 4`, `T = 64`; every `z_t` is `0` and the regret `1/2` exceeds `32/65`. The
hypothesis `hgω` repairs this by requiring `∇ω(z)` to give the one-sided derivative of `ω` along
`Z`, as a gradient does. It excludes `ω` with a kink where the selection is not this derivative.
For convex `ω` it implies that `∇ω(z)` is a subgradient on `Z`.

**Formalization Note** `Z` lives in a finite-dimensional real normed space `E` with an arbitrary norm. A
(sub)gradient is a continuous linear functional, `⟨g, v⟩` is `g v`, and `‖g‖_*` is the operator
norm `sup {g v : ‖v‖ ≤ 1}` (the paper's p.6 prints "min" and "‖x‖ ≤ 1", a misprint). Functions on
`Z` are total functions on `E` of which only the values on `Z` are used. Rounds are `t = 1, …, T`
(index `0` unused); each argmin is membership in `Z` plus `IsMinOn`, with no uniqueness, and only
`z_1, …, z_T` are constrained. The regret bound is stated against every comparator `u ∈ Z`, which
is the bound on (14). The losses are arbitrary, so they may depend on the iterates.
`θ_t = t`, and the step carries no further factor `θ_t`. `α`, `ω`, `G` are common to all rounds.
Convexity of `Z` is part of `ConvexOn ℝ Z ω`; convexity of each `h_t` follows from that of
`h_t - αω` and `ω`. -/
theorem theorem_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (ω : E → ℝ) (hω : ConvexOn ℝ Z ω) (gω : E → E →L[ℝ] ℝ)
    (hgω : IsDirectionalGradientOn Z ω gω)
    (hωa : ∀ z ∈ Z, ∀ z' ∈ Z, ‖z - z'‖ ^ 2 ≤ (gω z - gω z') (z - z'))
    (T : ℕ) (hT : 1 ≤ T) (α : ℝ) (hα : 0 < α)
    (h : ℕ → E → ℝ) (hrel : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Z (fun w => h t w - α * ω w))
    (gh : ℕ → E → E →L[ℝ] ℝ)
    (hgh : ∀ t ∈ Finset.Icc 1 T, ∀ w ∈ Z,
      ModernOnlineLearning.OMD.IsSubgradientOn Z (h t) w (gh t w))
    (G : ℝ) (hghG : ∀ t ∈ Finset.Icc 1 T, ∀ w ∈ Z, ‖gh t w‖ ≤ G)
    (z : ℕ → E) (hz : ∀ t ∈ Finset.Icc 1 T, z t ∈ Z) (hz1 : IsMinOn ω Z (z 1))
    (hstep : ∀ t ∈ Finset.Ico 1 T,
      IsMinOn (fun w => ((2 / (α * ((t : ℝ) + 1))) • gh t (z t) - gω (z t)) w + ω w)
        Z (z (t + 1))) :
    ∀ u ∈ Z, weightedRegretAgainst T (fun t => (t : ℝ)) h z u ≤
      2 * G ^ 2 / (α * ((T : ℝ) + 1)) := by sorry

end DynChoiceJEO.Supplement
