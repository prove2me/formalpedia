-- Prove2me | Theorems.Thm_ChenWhitt93_JumpDiffusion_lemma_4_1
-- name    : ChenWhitt93.JumpDiffusion.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:50:08.140194+00:00
-- url     : https://prove2.me/theorems/6f0b989d-7000-4cb1-a495-b6cafd26e697
-- title:
--   Lemma 4.1 — the scaled cumulative down time converges to $\hat D$ in $D((0,\infty),\mathbb R^J,M_1)$
-- statement:
--   For each $n$, let $(u^{j,n}_k,d^{j,n}_k)_{1\le j\le J,\,k\ge 1}$ be the up and down durations of network $n$. They are random variables on a probability space $(\Omega,\mathbb P)$, nonnegative, and almost surely have finitely many cycles in finite time. Let $(u^j_k,d^j_k)$ be random variables on $(\Omega',\mathbb P')$. Assume
--
--   1. (4.5): $\big(u^{j,n}_k/n,\ d^{j,n}_k/\sqrt n\big)_{j,k}\Rightarrow(u^j_k,d^j_k)_{j,k}$ in $(\mathbb R^{2J})^\infty$;
--   2. $\sum_{k=1}^m u^j_k\to\infty$ as $m\to\infty$, almost surely, for each $j$;
--   3. (4.11): almost surely no two distinct coordinates of $\hat D$ have a common discontinuity.
--
--   Let $\hat D^n_j(t)=n^{-1/2}D^n_j(nt)$ be the scaled cumulative down time of network $n$, and $\hat D$ the process (4.9). Then
--   $$
--   \hat D^n\Rightarrow\hat D\quad\text{in }D((0,\infty),\mathbb R^J,M_1).
--   $$
--
--   The limit $\hat D$ is a pure-jump process: a down period of order $\sqrt n$ lasts only $n^{-1/2}$ in the time scale $t$ and becomes a jump. The lemma supplies the jump part (4.25) of the limit free process in the proof of Theorem 4.1. The time interval is open because $\hat D^n(0)=0$, while $\hat D(0)$ can be positive when $u^j_1=0$ (Remark (4.2)).
--
--   **Formalization Note** Weak convergence is written in coupling form: some probability space carries copies of the prelimits (for large $n$) and of the limit with the same laws, and on it the convergence holds almost surely. The convergence is $M_1$ convergence on every $[a,b]$ with $0<a<b$ continuity points of the limit, with one parametric representation for all $J$ coordinates. The durations are indexed from $k=0$ in Lean.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 348, Lemma 4.1 (with (4.5), p. 347, and (4.9)–(4.11), p. 348)

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_HeavyTraffic

namespace ChenWhitt93.JumpDiffusion

open Filter Topology MeasureTheory Matrix

/-- Lemma 4.1 (p. 348): if the scaled up/down durations converge jointly in distribution (4.5),
the limit up durations have divergent partial sums, and (4.11) holds, then
`D̂ⁿ ⇒ D̂` in `D((0, ∞), ℝᴶ, M₁)`. -/
theorem lemma_4_1 {J : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (I : ℕ → Ω → Interruptions J) (uh dh : Ω' → Fin J → ℕ → ℝ)
    (hmeas : ∀ n j k, Measurable (fun ω => (I n ω).up j k) ∧ Measurable (fun ω => (I n ω).down j k))
    (hmeas' : ∀ j k, Measurable (fun ω => uh ω j k) ∧ Measurable (fun ω => dh ω j k))
    (hvalid : ∀ n, ∀ᵐ ω ∂P, (I n ω).IsValid)
    (h45 : CouplingConverges (fun w w' => Tendsto w atTop (𝓝 w')) P
      (fun n ω => fun j k => ((I n ω).up j k / n, (I n ω).down j k / Real.sqrt n)) P'
      (fun ω => fun j k => (uh ω j k, dh ω j k)))
    (hsum : ∀ᵐ ω ∂P', ∀ j, Tendsto (fun m => ∑ k ∈ Finset.range m, uh ω j k) atTop atTop)
    (h411 : ∀ᵐ ω ∂P', NoCommonJumps (downHat (uh ω) (dh ω))) :
    CouplingConverges M1Tendsto P (fun n ω => downScaled (I n ω) n) P'
      (fun ω => downHat (uh ω) (dh ω)) := by sorry

end ChenWhitt93.JumpDiffusion
