-- Prove2me | Theorems.Thm_ChenWhitt93_JumpDiffusion_eq_4_29
-- name    : ChenWhitt93.JumpDiffusion.eq_4_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:53:23.569063+00:00
-- url     : https://prove2.me/theorems/96270d5a-1caf-4788-acb5-c8d51d22c222
-- title:
--   Eqs. (4.28)–(4.29) — $(n^{-1/2}X^n(nt),n^{-1/2}D^n(nt))\to(\hat X,\hat D)$ in $D((0,\infty),\mathbb R^{2J},M_1)$
-- statement:
--   Assume the deterministic hypotheses of the proof of Theorem 4.1, as in Lemma 4.2, and let $(Z^n,B^n)$ solve (3.2)–(3.3) for network $n$. Let $X^n=Z^n(0)+\xi^n+\eta^n$ be the free process (3.11) of network $n$ and $D^n$ its cumulative down time. Then
--   $$
--   \Big(\frac1{\sqrt n}X^n(nt),\ \frac1{\sqrt n}D^n(nt)\Big)\to\big(\hat X(t),\hat D(t)\big)\qquad\text{in }D((0,\infty),\mathbb R^{2J},M_1),
--   $$
--   where $\hat X(t)=\hat Z(0)+\hat\xi(t)+\hat\eta(t)$ is given by (4.14)–(4.16) and $\hat D$ by (4.9). The convergence is joint, with a single parametric representation for all $2J$ coordinates. In particular $n^{-1/2}X^n(nt)\to\hat X(t)$ in $D((0,\infty),\mathbb R^J,M_1)$ (4.28).
--
--   This is the convergence of the input of the reflection map. The limit $\hat X$ has jumps in the directions $[I-P^{\mathsf t}]\operatorname{diag}(\mu)e_j$ at the jump times of $\hat D_j$.
--
--   **Formalization Note** The stacked path takes values in $(\mathbb R^J)^2$ with the sup norm. $M_1$ convergence on $(0,\infty)$ is convergence on every $[a,b]$ whose endpoints $0<a<b$ are continuity points of the limit.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), pp. 352–353, Eqs. (4.28)–(4.29) (with (3.10)–(3.11), p. 346, and (4.14)–(4.16), p. 350)

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_HeavyTraffic

namespace ChenWhitt93.JumpDiffusion

open Filter Topology MeasureTheory Matrix

/-- Eqs. (4.28)–(4.29) (pp. 352–353): under the pathwise assumptions of the proof of Theorem 4.1,
`(n^{-1/2} Xⁿ(nt), n^{-1/2} Dⁿ(nt)) → (X̂(t), D̂(t))` in `D((0, ∞), ℝ^{2J}, M₁)` (a single
parametric representation for all `2J` coordinates), with `Xⁿ` of (3.11), `X̂` of (4.14) and
`D̂` of (4.9). -/
theorem eq_4_29 {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (net : ℕ → NetworkData J)
    (lamn mun : ℕ → Fin J → ℝ) (lam mu clam cmu : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ)
    (L : LimitData J) (Z : ℕ → ℝ → Fin J → ℤ) (B : ℕ → ℝ → Fin J → ℝ)
    (hH : PathwiseHyp χ net lamn mun lam mu clam cmu P L)
    (hsol : ∀ n, IsQueueSolution χ (net n) (Z n) (B n)) :
    M1Tendsto
      (fun (n : ℕ) (t : ℝ) =>
        (![(Real.sqrt n)⁻¹ • freeProcess χ (net n) (lamn n) (mun n) P (B n) (n * t),
            downScaled (net n).toInterruptions n t] : Fin 2 → Fin J → ℝ))
      (fun t => ![XHat L mu clam cmu P t, downHat L.up L.down t]) := by sorry

end ChenWhitt93.JumpDiffusion
