-- Prove2me | Theorems.Thm_ChenWhitt93_JumpDiffusion_theorem_4_1_J1
-- name    : ChenWhitt93.JumpDiffusion.theorem_4_1_J1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:56:12.068717+00:00
-- url     : https://prove2.me/theorems/560cf4a3-cad9-4700-b356-f54a1664cdd8
-- title:
--   Theorem 4.1 (case J = 1) — jump-diffusion heavy-traffic limit for a single station with long up and down times
-- statement:
--   This is Theorem 4.1 for a network with a single station ($J=1$). The routing matrix is then a number $P=p\in[0,1)$ (feedback), and the reflection map is the one-dimensional reflection with $Q=p$.
--
--   Consider a sequence of single-station queues with exogenous service interruptions, all on a probability space $(\Omega,\mathbb P)$ and all with the same routing. Queue $n$ has primitive data $Z^n(0),A^n,S^n$ and up and down durations $(u^{n}_k,d^{n}_k)$. These are random and satisfy the standing assumptions of Section 3 almost surely. Its queue length and busy time $(Z^n,B^n)$ solve (3.2)–(3.3) almost surely. Assume the assumptions of Section 4(A):
--
--   1. jointly in $n$, as $n\to\infty$,
--   $$
--   \tfrac1{\sqrt n}Z^n(0)\Rightarrow\hat Z(0),\quad \tfrac1{\sqrt n}[A^n(nt)-\lambda^nnt]\Rightarrow\hat A(t),\quad \tfrac1{\sqrt n}[S^n(nt)-\mu^nnt]\Rightarrow\hat S(t),
--   $$
--   $$
--   \tfrac1{\sqrt n}[R(\lfloor nt\rfloor)-pnt]\Rightarrow\hat R(t),\quad \Big\{\Big(\tfrac{u^{n}_k}{n},\tfrac{d^{n}_k}{\sqrt n}\Big)\Big\}\Rightarrow\{(u_k,d_k)\}, \qquad (4.1)\text{–}(4.5)
--   $$
--   where the limits live on a probability space $(\Omega',\mathbb P')$, $\hat A,\hat S,\hat R$ have continuous sample paths and $\sum_{k=1}^mu_k\to\infty$ almost surely;
--   2. (4.6)–(4.8): $\sqrt n(\lambda^n-\lambda)\to c_\lambda$ with $\lambda\ge 0$, $\sqrt n(\mu^n-\mu)\to c_\mu$ with $\mu>0$, and $\lambda=(1-p)\mu$ with $0\le p$ and $p^k\to 0$.
--
--   Let $\hat X(t)=\hat Z(0)+\hat\xi(t)+(c_\lambda-(1-p)c_\mu)t+(1-p)\mu\hat D(t)$ be given by (4.14)–(4.16). Let $\hat Z=\phi(\hat X)$ and $\hat Y=\mu^{-1}\psi(\hat X)$ (4.13), and $\hat B=-\hat D-\hat Y$ (4.17), with $\hat D$ as in (4.9). Then
--   $$
--   (\hat Z^n,\hat B^n,\hat Y^n,\hat D^n)\Rightarrow(\hat Z,\hat B,\hat Y,\hat D)\qquad\text{in }D((0,\infty),\mathbb R^{4},M_1),
--   $$
--   where $\hat Z^n(t)=n^{-1/2}Z^n(nt)$, $\hat Y^n(t)=n^{-1/2}Y^n(nt)$, $\hat B^n(t)=n^{-1/2}[B^n(nt)-nt]$ and $\hat D^n(t)=n^{-1/2}D^n(nt)$.
--
--   Up times of order $n$ and down times of order $\sqrt n$ produce a reflected jump-diffusion limit. It extends the single-station heavy-traffic limit of Kella and Whitt to a station with feedback.
--
--   **Formalization Note** The Lean statement is the printed Theorem 4.1 with `Fin J` replaced by `Fin 1`; with one station, (4.11) holds trivially. The printed theorem claims strong $M_1$ convergence (one parametric representation for all $4J$ coordinates) for every $J$; that claim fails for $J\ge 2$, where a downstream queue that empties part-way through an upstream outage bends the prelimit graph of the jump, so the mission's goal is the case $J=1$. Weak convergence is written in coupling form, both for the joint hypotheses (4.1)–(4.5) and for the conclusion; the hypotheses' limits are continuous, so their mode is u.o.c. on $[0,\infty)$ for the paths and coordinatewise convergence for the durations. The conclusion's mode is strong $M_1$ convergence on $(0,\infty)$, on every $[a,b]$ with $0<a<b$ continuity points of the limit. The statement quantifies over every solution $(Z^n,B^n)$ and every reflection pair $(\mu\hat Y,\hat Z)$ of $\hat X$; $Z^n,B^n,\hat Z,\hat Y$ are assumed to be stochastic processes (each coordinate at each time $t\ge 0$ a random variable). All queues are placed on one probability space so that the routing is literally the same; only the laws of each queue enter.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 350, Theorem 4.1, (4.12)–(4.17), specialised to J = 1, with the assumptions of Section 4(A), pp. 347–348, (4.1)–(4.8), and (4.9), p. 348

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_HeavyTraffic

namespace ChenWhitt93.JumpDiffusion

open Filter Topology MeasureTheory Matrix

/-- Theorem 4.1 (p. 350), the case of a single station (`J = 1`): if (4.11) and the assumptions of Section 4(A) hold, then
`(Ẑⁿ, B̂ⁿ, Ŷⁿ, D̂ⁿ) ⇒ (Ẑ, B̂, Ŷ, D̂)` in `D((0, ∞), ℝ⁴, M₁)`, where `Ẑ = φ(X̂)`,
`Ŷ = diag(μ⁻¹)ψ(X̂)` for the reflection map `(ψ, φ)` with `Q = Pᵗ`, `X̂` is (4.14)–(4.16),
`B̂ = −D̂ − Ŷ` (4.17) and `D̂` is (4.9). Weak convergence is written in coupling form, for the
hypotheses (4.1)–(4.5) (jointly) and for the conclusion. -/
theorem theorem_4_1_J1 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Pr' : Measure Ω') [IsProbabilityMeasure Pr']
    (χ : Ω → Fin 1 → Fin 1 → ℕ → Bool) (net : ℕ → Ω → NetworkData 1)
    (Z : ℕ → Ω → ℝ → Fin 1 → ℤ) (B : ℕ → Ω → ℝ → Fin 1 → ℝ)
    (lamn mun : ℕ → Fin 1 → ℝ) (lam mu clam cmu : Fin 1 → ℝ) (P : Matrix (Fin 1) (Fin 1) ℝ)
    (L : Ω' → LimitData 1) (Zh Yh : Ω' → ℝ → Fin 1 → ℝ)
    -- Section 3: each network's primitive data are random and satisfy the model's assumptions,
    -- and `(Zⁿ, Bⁿ)` solves (3.2)–(3.3)
    (hrand : IsRandomNetwork χ net)
    (hvalid : ∀ n, ∀ᵐ ω ∂Pr, (net n ω).IsValid (χ ω))
    (hsol : ∀ n, ∀ᵐ ω ∂Pr, IsQueueSolution (χ ω) (net n ω) (Z n ω) (B n ω))
    (hZBmeas : ∀ n t, 0 ≤ t → ∀ j, Measurable (fun ω => Z n ω t j) ∧ Measurable (fun ω => B n ω t j))
    -- Section 4(A): (4.6)–(4.8)
    (hpar : ParamHyp lamn mun lam mu clam cmu P)
    -- Section 4(A): (4.1)–(4.5) jointly, with limits of the stated regularity, and (4.11)
    (hLmeas : Measurable (fun ω' => (L ω').toPrim))
    (hjoint : CouplingConverges PrimConv Pr
      (fun n ω => scaledPrimitives (χ ω) (net n ω) (lamn n) (mun n) P n) Pr'
      (fun ω' => (L ω').toPrim))
    (hreg : ∀ᵐ ω' ∂Pr', LimitRegular (L ω'))
    -- the limit: `(diag(μ)Ŷ, Ẑ) = (ψ(X̂), φ(X̂))`
    (hZYmeas : ∀ t, 0 ≤ t → ∀ j, Measurable (fun ω' => Zh ω' t j) ∧ Measurable (fun ω' => Yh ω' t j))
    (hrefl : ∀ᵐ ω' ∂Pr',
      IsReflection P.transpose (XHat (L ω') mu clam cmu P) (fun t => mu * Yh ω' t) (Zh ω')) :
    CouplingConverges M1Tendsto Pr (fun n ω => jointScaled (net n ω) (Z n ω) (B n ω) n) Pr'
      (fun ω' => jointLimit (L ω') (Zh ω') (Yh ω')) := by sorry

end ChenWhitt93.JumpDiffusion
