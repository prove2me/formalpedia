-- Prove2me | Theorems.Thm_DynChoiceJEO_Supplement_theorem_3
-- name    : DynChoiceJEO.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:13:38.734593+00:00
-- url     : https://prove2.me/theorems/dfc923a8-fe99-4cca-bcc0-dd8c0f0d607a
-- title:
--   Theorem 3 (corrected: $\nabla\omega$ is the directional derivative) — online mirror descent has weighted regret $\le\sqrt{2\Omega G^2\sum_t(\theta_t/\Theta_T)^2}$
-- statement:
--   Let $E$ be a finite-dimensional real normed space with an arbitrary norm $\|\cdot\|$, let $\langle g,v\rangle$ be the value of a linear functional $g$ at $v$, and let $\|g\|_*=\sup\{\langle g,v\rangle:\|v\|\le1\}$ be the dual norm. A **subgradient on $Z\subseteq E$** of $f$ at $z\in Z$ is a functional $g$ with $f(u)\ge f(z)+\langle g,u-z\rangle$ for all $u\in Z$.
--
--   Let $Z\subseteq E$ be convex and $\omega:Z\to\mathbb R$ convex, with a selection $\nabla\omega$ that represents its one-sided derivatives along $Z$, that is, $\lim_{s\to0^+}[\omega(z+s(u-z))-\omega(z)]/s=\langle\nabla\omega(z),u-z\rangle$ for $z,u\in Z$. Assume
--
--   - (3a) $\langle\nabla\omega(z)-\nabla\omega(z'),z-z'\rangle\ge\|z-z'\|^2$ for $z,z'\in Z$;
--   - (3b) $\omega(z)-\omega(z')\le\Omega$ for $z,z'\in Z$, where $\Omega>0$.
--
--   For $t\in[T]$ let $h_t:Z\to\mathbb R$ be convex and let $\nabla h_t(z)$ be a subgradient on $Z$ at every $z\in Z$ with $\|\nabla h_t(z)\|_*\le G$, where $G>0$. Let $\theta_t\ge0$ with $\Theta_T=\sum_{t\in[T]}\theta_t>0$, put $\gamma=\sqrt{2\Omega/(G^2\sum_{t\in[T]}\theta_t^2)}$, and let
--
--   $$
--   z_1\in\arg\min_{z\in Z}\omega(z),\qquad z_{t+1}\in\arg\min_{z\in Z}\{\langle\gamma\theta_t\nabla h_t(z_t)-\nabla\omega(z_t),z\rangle+\omega(z)\}\quad(1\le t<T).
--   $$
--
--   Then
--
--   1. the weighted regret satisfies
--   $$
--   \frac1{\Theta_T}\sum_{t\in[T]}\theta_th_t(z_t)-\min_{z\in Z}\frac1{\Theta_T}\sum_{t\in[T]}\theta_th_t(z)\le\sqrt{2\Omega G^2\sum_{t\in[T]}\Big(\frac{\theta_t}{\Theta_T}\Big)^2};
--   $$
--   2. if $\theta_t=1$ for all $t\in[T]$, it is at most $\sqrt{2\Omega G^2/T}$.
--
--   With $Z=Y$ and $h_t=-\Psi(x_t,\cdot;p_t)$ this bounds the dual regret in the primal-oracle scheme, giving an $O(1/\sqrt T)$ rate for uniform weights.
--
--   The paper allows $\nabla\omega$ to be any subgradient selection, and the statement is then false: on $Z=[-1,1]$ with $\omega(z)=z^2/2+|z|$, $\nabla\omega(0)=-1$, $h_t(z)=-z$, $\theta_t=1$ and $T=4$, every iterate is $0$ and the regret $1$ exceeds $\sqrt3/2$.
--
--   **Formalization Note** Functions on $Z$ are total functions on $E$ of which only the values on $Z$ are used. Each argmin means membership in $Z$ together with minimality on $Z$; existence and uniqueness are not assumed, and only $z_1,\dots,z_T$ are constrained. The regret bound is stated against every comparator in $Z$, which is the same bound on the weighted regret (14). The losses are arbitrary and may depend on the iterates.
--
--   Differences from the source:
--
--   - correction: ∇ω(z) is the gradient where ω is differentiable and otherwise any subgradient (p.6) → ∇ω represents the one-sided derivatives of ω along Z (IsDirectionalGradientOn), which implies the subgradient property for convex ω; reason: false as printed: Z = [−1,1], ω = z²/2 + |z|, ∇ω(0) = −1, ∇ω(z) = z + sgn z otherwise, h_t = −z, θ_t = 1, T = 4, Ω = 3/2, G = 1 gives regret 1 > √3/2. Excluded cases: a kinked ω whose selection is not this derivative; every gradient of a differentiable ω is covered
--   - encoding: Euclidean space containing Z with some norm ∥·∥, inner product ⟨·,·⟩ → finite-dimensional real normed space E; gradients are continuous linear functionals and ⟨g,v⟩ is g v; reason: a linear functional is the same as a vector paired by the inner product; same instances
--   - correction: dual norm ∥x∥∗ := min_y{⟨x,y⟩ : ∥x∥ ≤ 1} (p.6) → the operator norm, max_y{⟨x,y⟩ : ∥y∥ ≤ 1}; reason: misprint: as printed y is unconstrained, so for x ≠ 0 with ∥x∥ ≤ 1 the minimum is −∞ and is not a norm
--   - encoding: functions ω, h_t : Z → ℝ, Z convex → total functions on E used only on Z; convexity of Z is part of ConvexOn ℝ Z ω; reason: every function on Z extends arbitrarily; same instances
--   - encoding: a subgradient of a function defined on Z → the inequality f(u) ≥ f(z) + g(u − z) for all u ∈ Z; reason: the subgradient of a function with domain Z; same instances
--   - encoding: weighted regret (14), with min over z ∈ Z, at most B → weightedRegretAgainst at most B for every u ∈ Z; reason: equivalent, and free of junk values of a real infimum
--   - encoding: argmin, with z_{t+1} written as equal to it → membership in Z and IsMinOn, for z_1,…,z_T only; reason: same runs: the objective is strictly convex under Assumption 3(a), so a minimizer is unique, and z_{T+1} does not enter the claim
--   - reading: the weight sequence {θ_t} → θ_t ≥ 0 on [T]; reason: the weights are non-negative (p.10, step 3; p.ec7)
--   - encoding: division by Θ_T and by G² Σθ_t² in γ, with G < ∞ → hypotheses 0 < Σθ_t and 0 < G; reason: exclude only the cases where the printed expressions are undefined; T ≥ 1 follows
-- source:
--   Ho-Nguyen & Kılınç-Karzan, Dynamic Data-Driven Estimation of Non-Parametric Choice Models, arXiv:1702.05702v5, Theorem 3, p.15; Assumptions 2 and 3, p.15; eq. (14), p.15; Notation, p.6; proof, p.ec2 (PDF 24)

import Mathlib
import Definitions.Def_ModernOnlineLearning_OMD_Defs
import Definitions.Def_DynChoiceJEO_Supplement_weightedRegretAgainst
import Definitions.Def_DynChoiceJEO_Supplement_IsDirectionalGradientOn

namespace DynChoiceJEO.Supplement

/-- **Theorem 3 (corrected: `∇ω` is the directional derivative of `ω` along `Z`): online mirror
descent for convex losses.**
Ho-Nguyen & Kılınç-Karzan, *Dynamic Data-Driven Estimation of Non-Parametric Choice Models*,
arXiv:1702.05702v5, Theorem 3, p.15: "Suppose that Z satisfies Assumption 3(a,b), and that for all t ∈ [T],
h_t is convex and that Assumption 2 holds for h_t. Given the weight sequence {θ_t}_{t∈[T]},
compute z_1 ∈ arg min_{z∈Z} ω(z), z_{t+1} = arg min_{z∈Z} {⟨γθ_t∇h_t(z_t) − ∇ω(z_t), z⟩ + ω(z)},
where γ = √(2Ω/(G² ∑_{t∈[T]} θ_t²)). Then (1/Θ_T) ∑ θ_t h_t(z_t) − min_{z∈Z} (1/Θ_T) ∑ θ_t h_t(z)
≤ √(2ΩG² ∑_{t∈[T]} (θ_t/Θ_T)²). Furthermore, when θ_t = 1, the upper bound on regret becomes
√(2ΩG²/T)."
Assumption 2, p.15: "There exists a G < ∞ such that for any z ∈ Z, ‖∇h(z)‖_* ≤ G."
Assumption 3, p.15: "There exists a convex function ω : Z → ℝ satisfying: (a) for any z,z′ ∈ Z,
⟨∇ω(z) − ∇ω(z′), z − z′⟩ ≥ ‖z − z′‖²; and (b) there exists Ω > 0 such that
for any z,z′ ∈ Z, ω(z) − ω(z′) ≤ Ω."

**Correction** The paper lets `∇ω(z)` be any subgradient (p.6). The statement is then false:
on `Z = [-1,1]` take `ω(z) = z²/2 + |z|`, `∇ω(0) = -1`, `h_t(z) = -z`, `θ_t = 1`, `T = 4`; every
`z_t` is `0` and the regret `1` exceeds `√3/2`. The hypothesis `hgω` repairs this by requiring
`∇ω(z)` to give the one-sided derivative of `ω` along `Z`, as a gradient does. It excludes `ω`
with a kink where the selection is not this derivative. For convex `ω` it implies that `∇ω(z)`
is a subgradient on `Z`.

**Formalization Note** `Z` lives in a finite-dimensional real normed space `E` with an arbitrary norm. A
(sub)gradient is a continuous linear functional, `⟨g, v⟩` is `g v`, and `‖g‖_*` is the operator
norm `sup {g v : ‖v‖ ≤ 1}` (the paper's p.6 prints "min" and "‖x‖ ≤ 1", a misprint). Functions on
`Z` are total functions on `E` of which only the values on `Z` are used. Rounds are `t = 1, …, T`
(index `0` unused); each argmin is membership in `Z` plus `IsMinOn`, with no uniqueness, and only
`z_1, …, z_T` are constrained. The regret bound is stated against every comparator `u ∈ Z`, which
is the bound on (14). The losses are arbitrary, so they may depend on the iterates.
`G > 0` and `Θ_T > 0` only exclude the cases where `γ` or the averages are undefined. Convexity of
`Z` is part of `ConvexOn ℝ Z ω`. -/
theorem theorem_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (ω : E → ℝ) (hω : ConvexOn ℝ Z ω) (gω : E → E →L[ℝ] ℝ)
    (hgω : IsDirectionalGradientOn Z ω gω)
    (hωa : ∀ z ∈ Z, ∀ z' ∈ Z, ‖z - z'‖ ^ 2 ≤ (gω z - gω z') (z - z'))
    (Ω : ℝ) (hΩ : 0 < Ω) (hωb : ∀ z ∈ Z, ∀ z' ∈ Z, ω z - ω z' ≤ Ω)
    (T : ℕ) (θ : ℕ → ℝ) (hθ : ∀ t ∈ Finset.Icc 1 T, 0 ≤ θ t)
    (hΘ : 0 < ∑ t ∈ Finset.Icc 1 T, θ t)
    (h : ℕ → E → ℝ) (hconvex : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Z (h t))
    (gh : ℕ → E → E →L[ℝ] ℝ)
    (hgh : ∀ t ∈ Finset.Icc 1 T, ∀ w ∈ Z,
      ModernOnlineLearning.OMD.IsSubgradientOn Z (h t) w (gh t w))
    (G : ℝ) (hG : 0 < G) (hghG : ∀ t ∈ Finset.Icc 1 T, ∀ w ∈ Z, ‖gh t w‖ ≤ G)
    (z : ℕ → E) (hz : ∀ t ∈ Finset.Icc 1 T, z t ∈ Z) (hz1 : IsMinOn ω Z (z 1))
    (hstep : ∀ t ∈ Finset.Ico 1 T,
      IsMinOn
        (fun w => ((Real.sqrt (2 * Ω / (G ^ 2 * ∑ s ∈ Finset.Icc 1 T, θ s ^ 2)) * θ t) • gh t (z t)
            - gω (z t)) w + ω w)
        Z (z (t + 1))) :
    (∀ u ∈ Z, weightedRegretAgainst T θ h z u ≤
        Real.sqrt (2 * Ω * G ^ 2 *
          ∑ t ∈ Finset.Icc 1 T, (θ t / ∑ s ∈ Finset.Icc 1 T, θ s) ^ 2)) ∧
      ((∀ t ∈ Finset.Icc 1 T, θ t = 1) →
        ∀ u ∈ Z, weightedRegretAgainst T θ h z u ≤ Real.sqrt (2 * Ω * G ^ 2 / T)) := by sorry

end DynChoiceJEO.Supplement
