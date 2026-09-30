-- Prove2me | Theorems.Thm_ChenWhitt93_JumpDiffusion_theorem_4_1_pathwise_J1
-- name    : ChenWhitt93.JumpDiffusion.theorem_4_1_pathwise_J1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:54:10.643297+00:00
-- url     : https://prove2.me/theorems/126516b0-1048-4966-990a-07c0804f25af
-- title:
--   Proof of Theorem 4.1, p. 351 (case J = 1) — the almost-sure core, $(\hat Z^n,\hat B^n,\hat Y^n,\hat D^n)\to(\hat Z,\hat B,\hat Y,\hat D)$ in $D((0,\infty),\mathbb R^{4},M_1)$
-- statement:
--   Consider a single station ($J=1$) with feedback routing probability $P=p$. Assume the deterministic hypotheses of the proof of Theorem 4.1:
--
--   1. every network satisfies the standing assumptions of Section 3;
--   2. (4.6)–(4.8), so in particular $\lambda=(1-p)\mu$ with $0\le p<1$;
--   3. (4.18)–(4.22);
--   4. $\hat A,\hat S,\hat R$ are continuous and $\sum_ku_k=\infty$.
--
--   Let $(Z^n,B^n)$ solve (3.2)–(3.3) for network $n$. Let $\hat X$ be the limit free process (4.14)–(4.16), and let $(\hat Z,\hat Y)$ be paths such that $(\mu\hat Y,\hat Z)=(\psi(\hat X),\phi(\hat X))$ is the reflection of $\hat X$ associated with $Q=p$. Then
--   $$
--   (\hat Z^n,\hat B^n,\hat Y^n,\hat D^n)\to(\hat Z,\hat B,\hat Y,\hat D)\qquad\text{in }D((0,\infty),\mathbb R^{4},M_1),
--   $$
--   where $\hat Z^n(t)=n^{-1/2}Z^n(nt)$, $\hat B^n(t)=n^{-1/2}[B^n(nt)-nt]$, $\hat Y^n(t)=n^{-1/2}Y^n(nt)$, $\hat D^n(t)=n^{-1/2}D^n(nt)$, $\hat B=-\hat D-\hat Y$, and $\hat D$ is (4.9).
--
--   This is the statement that the proof of Theorem 4.1 establishes on a Skorohod representation space, specialised to one station. The goal (Theorem 4.1, case $J=1$) follows from it by passing back to laws.
--
--   **Formalization Note** The page states the display for general $J$ and prints the space as $D((-,\infty),\dots)$; it is $D((0,\infty),\dots)$, as in Theorem 4.1. The convergence is strong $M_1$: one parametric representation for all four coordinates. The general-$J$ strong-$M_1$ claim fails for $J\ge 2$ (a downstream queue that empties part-way through an upstream outage bends the prelimit graph of the jump), so the item is stated for $J=1$, the case of the mission's goal. The statement quantifies over every reflection pair of $\hat X$; see the Reflection definition for the treatment of $\hat X(0)<0$.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 351, proof of Theorem 4.1, display before (4.18), with (4.18)–(4.22), specialised to J = 1

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_HeavyTraffic

namespace ChenWhitt93.JumpDiffusion

open Filter Topology MeasureTheory Matrix

/-- The almost-sure core of the proof of Theorem 4.1 (p. 351, display before (4.18)), in the case
of a single station (`J = 1`): under (4.6)–(4.8) and (4.18)–(4.22) for deterministic paths (with
Section 3's assumptions on each network and Section 4(A)'s on the limit), for any queue-length /
busy-time pairs `(Zⁿ, Bⁿ)` and any reflection `(diag(μ)Ŷ, Ẑ) = (ψ(X̂), φ(X̂))` with `Q = Pᵗ`,
`(Ẑⁿ, B̂ⁿ, Ŷⁿ, D̂ⁿ) → (Ẑ, B̂, Ŷ, D̂)` in `D((0, ∞), ℝ⁴, M₁)`. -/
theorem theorem_4_1_pathwise_J1 (χ : Fin 1 → Fin 1 → ℕ → Bool) (net : ℕ → NetworkData 1)
    (lamn mun : ℕ → Fin 1 → ℝ) (lam mu clam cmu : Fin 1 → ℝ) (P : Matrix (Fin 1) (Fin 1) ℝ)
    (L : LimitData 1) (Z : ℕ → ℝ → Fin 1 → ℤ) (B : ℕ → ℝ → Fin 1 → ℝ)
    (Zh Yh : ℝ → Fin 1 → ℝ)
    (hH : PathwiseHyp χ net lamn mun lam mu clam cmu P L)
    (hsol : ∀ n, IsQueueSolution χ (net n) (Z n) (B n))
    (hrefl : IsReflection P.transpose (XHat L mu clam cmu P) (fun t => mu * Yh t) Zh) :
    M1Tendsto (fun n => jointScaled (net n) (Z n) (B n) n) (jointLimit L Zh Yh) := by sorry

end ChenWhitt93.JumpDiffusion
