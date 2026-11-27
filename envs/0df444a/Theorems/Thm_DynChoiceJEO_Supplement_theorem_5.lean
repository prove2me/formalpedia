-- Prove2me | Theorems.Thm_DynChoiceJEO_Supplement_theorem_5
-- name    : DynChoiceJEO.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:14:46.383554+00:00
-- url     : https://prove2.me/theorems/8637347d-5154-5fa1-824d-771e1bc299bc
-- title:
--   Theorem 5 (corrected: update adds $\theta_{t+1}\alpha\omega$) — follow-the-leader has weighted regret $\le 2G^2/(\alpha(T+1))$
-- statement:
--   Let $E$ be a finite-dimensional real normed space with an arbitrary norm $\|\cdot\|$, let $\langle g,v\rangle$ be the value of a linear functional $g$ at $v$, and let $\|g\|_*=\sup\{\langle g,v\rangle:\|v\|\le1\}$ be the dual norm. A **subgradient on $Z\subseteq E$** of $f$ at $z\in Z$ is a functional $g$ with $f(u)\ge f(z)+\langle g,u-z\rangle$ for all $u\in Z$.
--
--   Let $Z\subseteq E$ be convex and $\omega:Z\to\mathbb R$ convex, with a subgradient selection $\nabla\omega$ on $Z$ satisfying $\langle\nabla\omega(z)-\nabla\omega(z'),z-z'\rangle\ge\|z-z'\|^2$ (Assumption 3(a)).
--
--   Let $T\ge1$ and $\alpha>0$. For $t\in[T]$ let $h_t-\alpha\omega$ be convex on $Z$ (Assumption 4) and let $\nabla(h_t-\alpha\omega)(z)$ be a subgradient of $h_t-\alpha\omega$ on $Z$ at every $z\in Z$ with $\|\nabla(h_t-\alpha\omega)(z)\|_*\le G$ (Assumption 2 for $h_t-\alpha\omega$). Let $\theta_t=t$, so $\Theta_T=\sum_{t\in[T]}t$, and let
--
--   $$
--   z_1\in\arg\min_{z\in Z}\omega(z),\qquad z_{t+1}\in\arg\min_{z\in Z}\Big\{(t+1)\alpha\,\omega(z)+\sum_{s\in[t]}s\,h_s(z)\Big\}\quad(1\le t<T).
--   $$
--
--   Then
--
--   $$
--   \frac1{\Theta_T}\sum_{t\in[T]}t\,h_t(z_t)-\min_{z\in Z}\frac1{\Theta_T}\sum_{t\in[T]}t\,h_t(z)\le\frac{2G^2}{\alpha(T+1)} .
--   $$
--
--   Follow-the-leader with the regularizer of the coming round thus attains an $O(1/T)$ weighted regret, with a bound that involves only the subgradients of the parts $h_t-\alpha\omega$.
--
--   The paper prints the update $z_{t+1}=\arg\min_{z\in Z}\frac1{\Theta_t}\sum_{s\in[t]}\theta_sh_s(z)$, without the term $(t+1)\alpha\omega$, and the statement is then false: on $Z=[-1,1]$ with $\omega(z)=z^2/2$, $\alpha=1$, $T=2$, $h_1(z)=z^2/2+z$, $h_2(z)=z^2/2-z$ and $G=1$ it gives $z_2=-1$ and regret $19/18>2/3$. The corrected update is the one for which the bound in the paper's proof (p.ec2) applies.
--
--   **Formalization Note** Functions on $Z$ are total functions on $E$ of which only the values on $Z$ are used. Each argmin means membership in $Z$ together with minimality on $Z$; existence and uniqueness are not assumed, and only $z_1,\dots,z_T$ are constrained. The regret bound is stated against every comparator in $Z$, which is the same bound on the weighted regret (14). The losses are arbitrary and may depend on the iterates.
--
--   Differences from the source:
--
--   - correction: z_{t+1} = argmin over Z of (1/Θ_t) Σ_{s≤t} θ_s h_s → z_{t+1} minimizes θ_{t+1}αω + Σ_{s≤t} θ_s h_s over Z, with the same constant; reason: false as printed: Z = [−1,1], ω = z²/2, α = 1, T = 2, h_1 = z²/2 + z, h_2 = z²/2 − z, G = 1 gives regret 19/18 > 2/3; the proof on p.ec2 needs the regularizer of round t in the objective minimized by z_t. Excluded cases: none, the algorithm changes
--   - encoding: Euclidean space containing Z with some norm ∥·∥, inner product ⟨·,·⟩ → finite-dimensional real normed space E; gradients are continuous linear functionals and ⟨g,v⟩ is g v; reason: a linear functional is the same as a vector paired by the inner product; same instances
--   - correction: dual norm ∥x∥∗ := min_y{⟨x,y⟩ : ∥x∥ ≤ 1} (p.6) → the operator norm, max_y{⟨x,y⟩ : ∥y∥ ≤ 1}; reason: misprint: as printed y is unconstrained, so for x ≠ 0 with ∥x∥ ≤ 1 the minimum is −∞ and is not a norm
--   - encoding: functions ω, h_t : Z → ℝ, Z convex → total functions on E used only on Z; convexity of Z is part of ConvexOn ℝ Z ω; reason: every function on Z extends arbitrarily; same instances
--   - encoding: a subgradient of a function defined on Z → the inequality f(u) ≥ f(z) + g(u − z) for all u ∈ Z; reason: the subgradient of a function with domain Z; same instances
--   - encoding: weighted regret (14), with min over z ∈ Z, at most B → weightedRegretAgainst at most B for every u ∈ Z; reason: equivalent, and free of junk values of a real infimum
--   - encoding: argmin, with z_{t+1} written as equal to it → membership in Z and IsMinOn, for z_1,…,z_T only; reason: same runs: the objective is strictly convex under Assumption 3(a), so a minimizer is unique, and z_{T+1} does not enter the claim
--   - encoding: convex losses h_t (§4.2) → only h_t − αω convex, with ω convex and α > 0; reason: convexity of h_t follows from these; same instances
--   - encoding: horizon T ∈ ℕ with divisor Θ_T → hypothesis 1 ≤ T; reason: excludes only T = 0, where the averages are undefined
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, Theorem 5, p.16; Assumptions 2, 3(a) and 4, p.15; eq. (14), p.15; proof of Theorems 3, 4 and 5, p.ec2 (PDF 24)

import Mathlib
import Definitions.Def_ModernOnlineLearning_OMD_Defs
import Definitions.Def_DynChoiceJEO_Supplement_weightedRegretAgainst

namespace DynChoiceJEO.Supplement

/-- **Theorem 5 (corrected: the update includes `θ_{t+1}αω`): follow-the-leader.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*,
arXiv:1702.05702v5, Theorem 5, p.16: "Suppose that Z satisfies Assumption 3(a), and that for all t ∈ [T],
Assumption 4 holds for h_t, and Assumption 2 holds for h_t − αω. Let θ_t = t for all t ∈ [T], and
compute z_1 ∈ arg min_{z∈Z} ω(z), z_{t+1} = arg min_{z∈Z} {(1/Θ_t) ∑_{s∈[t]} θ_s h_s(z)}.
Then (1/Θ_T) ∑ θ_t h_t(z_t) − min_{z∈Z} (1/Θ_T) ∑ θ_t h_t(z) ≤ 2G²/(α(T+1))."
Assumption 2, p.15: "There exists a G < ∞ such that for any z ∈ Z, ‖∇h(z)‖_* ≤ G."
Assumption 3, p.15: "There exists a convex function ω : Z → ℝ satisfying: (a) for any z,z′ ∈ Z,
⟨∇ω(z) − ∇ω(z′), z − z′⟩ ≥ ‖z − z′‖²."
Assumption 4, p.15: "Let ω : Z → ℝ be a function satisfying Assumption 3(a). There exists α > 0
such that the function h − αω is convex."

**Correction** The printed update is false: on `Z = [-1,1]` take `ω(z) = z²/2`, `α = 1`, `T = 2`,
`h_1(z) = z²/2 + z`, `h_2(z) = z²/2 - z`, `G = 1`; it gives `z_2 = -1` and regret `19/18 > 2/3`.
The proof (p.ec2, PDF 24) applies Shalev-Shwartz and Kakade to `ℓ_t = θ_tαω + θ_t(h_t − αω)` with
the denominator `α ∑_{s∈[t]} θ_s`, so round `t`'s regularizer `θ_tαω` is already in the objective
that `z_t` minimizes. The corrected update is therefore that `z_{t+1}` minimizes
`θ_{t+1}αω + ∑_{s∈[t]} θ_s h_s` on `Z`; the constant is unchanged and no instance is excluded.

**Formalization Note** `Z` lives in a finite-dimensional real normed space `E` with an arbitrary norm. A
(sub)gradient is a continuous linear functional, `⟨g, v⟩` is `g v`, and `‖g‖_*` is the operator
norm `sup {g v : ‖v‖ ≤ 1}` (the paper's p.6 prints "min" and "‖x‖ ≤ 1", a misprint). Functions on
`Z` are total functions on `E` of which only the values on `Z` are used. Rounds are `t = 1, …, T`
(index `0` unused); each argmin is membership in `Z` plus `IsMinOn`, with no uniqueness, and only
`z_1, …, z_T` are constrained. The regret bound is stated against every comparator `u ∈ Z`, which
is the bound on (14). The losses are arbitrary, so they may depend on the iterates.
`θ_t = t`. `∇ω` is any subgradient selection of `ω` on `Z` satisfying Assumption 3(a), and
`∇(h_t − αω)` is any subgradient selection of `h_t − αω` on `Z` bounded by `G`. `α`, `ω`, `G` are
common to all rounds. Convexity of `Z` is part of `ConvexOn ℝ Z ω`; convexity of each `h_t`
follows from that of `h_t - αω` and `ω`. -/
theorem theorem_5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (ω : E → ℝ) (hω : ConvexOn ℝ Z ω) (gω : E → E →L[ℝ] ℝ)
    (hgω : ∀ w ∈ Z, ModernOnlineLearning.OMD.IsSubgradientOn Z ω w (gω w))
    (hωa : ∀ z ∈ Z, ∀ z' ∈ Z, ‖z - z'‖ ^ 2 ≤ (gω z - gω z') (z - z'))
    (T : ℕ) (hT : 1 ≤ T) (α : ℝ) (hα : 0 < α)
    (h : ℕ → E → ℝ) (hrel : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Z (fun w => h t w - α * ω w))
    (gφ : ℕ → E → E →L[ℝ] ℝ)
    (hgφ : ∀ t ∈ Finset.Icc 1 T, ∀ w ∈ Z,
      ModernOnlineLearning.OMD.IsSubgradientOn Z (fun v => h t v - α * ω v) w (gφ t w))
    (G : ℝ) (hgφG : ∀ t ∈ Finset.Icc 1 T, ∀ w ∈ Z, ‖gφ t w‖ ≤ G)
    (z : ℕ → E) (hz : ∀ t ∈ Finset.Icc 1 T, z t ∈ Z) (hz1 : IsMinOn ω Z (z 1))
    (hstep : ∀ t ∈ Finset.Ico 1 T,
      IsMinOn (fun w => ((t : ℝ) + 1) * α * ω w + ∑ s ∈ Finset.Icc 1 t, (s : ℝ) * h s w)
        Z (z (t + 1))) :
    ∀ u ∈ Z, weightedRegretAgainst T (fun t => (t : ℝ)) h z u ≤
      2 * G ^ 2 / (α * ((T : ℝ) + 1)) := by sorry

end DynChoiceJEO.Supplement
