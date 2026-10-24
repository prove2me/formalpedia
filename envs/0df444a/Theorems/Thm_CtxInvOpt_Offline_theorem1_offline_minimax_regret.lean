-- Prove2me | Theorems.Thm_CtxInvOpt_Offline_theorem1_offline_minimax_regret
-- name    : CtxInvOpt.Offline.theorem1_offline_minimax_regret
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:34.745859+00:00
-- url     : https://prove2.me/theorems/20ea0b1c-82b6-43da-9e5c-e7a78855996b
-- title:
--   Theorem 1, p. 12 — the circumcenter policy has worst-case regret ≤ sin α(C(D)) (or 1), and no policy does better on some C with α(C) = ᾱ
-- statement:
--   Let $n\ge1$ and $d\ge2$, and write $g(a)=\mathbf 1\{a<\pi/2\}\sin a+\mathbf 1\{a\ge\pi/2\}$.
--
--   1. **Upper bound.** Let $\mathcal D=\{(\mathcal X_i,f_i,x^\star_i)\}_{i=1}^N$ be an offline data set with $\mathcal X_i\in\mathcal B$, $f_i\in\mathcal F$, and suppose the data are realizable: there is $c_0\in S^d$ with $x^\star_i\in\psi(c_0,\mathcal X_i,f_i)$ for every $i$. Let $\hat c$ be any circumcenter of $C(\mathcal D)$. Then for every true cost $c^\star\in C(\mathcal D)$, every $\mathcal X\in\mathcal B$, every $f\in\mathcal F$, every action $x^\pi\in\psi(\hat c,\mathcal X,f)$ of the circumcenter policy and every optimal action $x^\star\in\psi(c^\star,\mathcal X,f)$,
--   $$\big(f(x^\pi)-f(x^\star)\big)'c^\star\ \le\ g\big(\alpha(C(\mathcal D))\big).$$
--   In other words $\mathcal{WCR}^\pi(\mathcal D)\le\mathbf 1\{\alpha(C(\mathcal D))<\pi/2\}\sin\alpha(C(\mathcal D))+\mathbf 1\{\alpha(C(\mathcal D))\ge\pi/2\}$.
--   2. **Lower bound.** For every $\bar\alpha\in[0,\pi]$ there is a nonempty information set $C\subseteq S^d$ with $\alpha(C)=\bar\alpha$ such that, for every policy $\pi$ (a map assigning to each instance $(\mathcal X,f)$ with $\mathcal X\in\mathcal B$, $f\in\mathcal F$ an action $x^\pi\in\mathcal X$), there are $c^\star\in C$, $\mathcal X\in\mathcal B$, $f\in\mathcal F$ and $x^\star\in\psi(c^\star,\mathcal X,f)$ with
--   $$\big(f(x^\pi)-f(x^\star)\big)'c^\star\ \ge\ g(\bar\alpha).$$
--   So no policy achieves worst-case regret lower than $\sin\bar\alpha$ if $\bar\alpha<\pi/2$, respectively $1$ if $\bar\alpha\ge\pi/2$.
--
--   Together, the two parts say that the uncertainty angle of the knowledge set determines the minimax offline regret, and that acting as if the cost were the circumcenter attains it.
--
--   **Formalization Note** The worst-case regret is never formed as a real supremum. Part 1 is stated for every admissible instance and every tie-breaking of the circumcenter policy; part 2 is stated in the attained form (some instance has regret at least $g(\bar\alpha)$), which implies the paper's bound on the supremum. The quantifier order of part 2 is: the set $C$, then the policy, then nature's instance. The policy is a map of the instance only because $C$ (the information) is fixed before it. The hypothesis $n\ge1$ is not written in the paper and is needed for part 2 ($\mathbb R^0$ is a single point); $d\ge2$ is the paper's standing assumption. Data are indexed by `Fin N`.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 12, Theorem 1 (with (2)–(4), pp. 7–8); proof App-7–App-9

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry
import Definitions.Def_CtxInvOpt_Offline_Data

namespace CtxInvOpt.Offline

/-- **Theorem 1 (Offline minimax regret), arXiv:2106.14015v3, p. 12.**
(a) For realizable offline data `D`, the circumcenter policy (any circumcenter `ĉ` of `C(D)`, any
minimizer `x^π ∈ ψ(ĉ, X, f)`) has regret at most `1{α(C(D)) < π/2} sin α(C(D)) + 1{α(C(D)) ≥ π/2}`
against every `c⋆ ∈ C(D)`, every `X ∈ 𝔅` and every `f ∈ 𝔉`.
(b) For every `ᾱ ∈ [0, π]` there is a nonempty information set `C ⊆ S^d` with `α(C) = ᾱ` such
that every policy incurs, on some instance `(c⋆, X, f)` with `c⋆ ∈ C`, regret at least
`sin ᾱ` (if `ᾱ < π/2`), respectively `1` (if `ᾱ ≥ π/2`). -/
theorem theorem1_offline_minimax_regret {n d N : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) :
    (∀ (Xs : Fin N → Set (EuclideanSpace ℝ (Fin n)))
        (fs : Fin N → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
        (xs : Fin N → EuclideanSpace ℝ (Fin n)),
        (∀ i, IsActionSet (Xs i)) → (∀ i, IsContext (fs i)) →
        ∀ c0 : EuclideanSpace ℝ (Fin d), c0 ∈ unitSphere d →
        (∀ i, xs i ∈ argminSet c0 (Xs i) (fs i)) →
        ∀ chat : EuclideanSpace ℝ (Fin d), IsCircumcenter (consistentSet Xs fs xs) chat →
        ∀ cstar ∈ consistentSet Xs fs xs,
        ∀ (X : Set (EuclideanSpace ℝ (Fin n)))
          (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)),
          IsActionSet X → IsContext f →
          ∀ xpi ∈ argminSet chat X f, ∀ xstar ∈ argminSet cstar X f,
            inner ℝ (f xpi - f xstar) cstar ≤ regretCap (uncAngle (consistentSet Xs fs xs))) ∧
    (∀ abar ∈ Set.Icc (0 : ℝ) Real.pi,
      ∃ C : Set (EuclideanSpace ℝ (Fin d)), C ⊆ unitSphere d ∧ C.Nonempty ∧ uncAngle C = abar ∧
        ∀ pol : Set (EuclideanSpace ℝ (Fin n)) →
            (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin n),
          (∀ X f, IsActionSet X → IsContext f → pol X f ∈ X) →
          ∃ cstar ∈ C, ∃ (X : Set (EuclideanSpace ℝ (Fin n)))
            (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d)),
            IsActionSet X ∧ IsContext f ∧
            ∃ xstar ∈ argminSet cstar X f,
              regretCap abar ≤ inner ℝ (f (pol X f) - f xstar) cstar) := by sorry

end CtxInvOpt.Offline
