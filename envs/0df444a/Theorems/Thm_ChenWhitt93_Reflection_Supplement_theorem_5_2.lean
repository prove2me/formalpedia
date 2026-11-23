-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_Supplement_theorem_5_2
-- name    : ChenWhitt93.Reflection.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:56:51.807529+00:00
-- url     : https://prove2.me/theorems/a68a8248-9ef8-4a05-b0f6-880a573c7d49
-- title:
--   Theorem 5.2 — heavy-traffic J₁ limit for open networks with fixed up and down times
-- statement:
--   Consider a sequence of open networks with $J$ stations and exogenous service interruptions, indexed by $n$, with a common routing $R^n=R$ and routing matrix $P$, and let $(Z^n,B^n)$ be the queue-length and busy-time processes and $Y^n$ the idle time of network $n$. Assume all of Section 4(A) except (4.5) and (4.8):
--
--   1. (4.1)–(4.4) hold jointly with (5.1): $\tfrac{1}{\sqrt n}Z^n(0)\Rightarrow\hat Z(0)$, $\tfrac{1}{\sqrt n}[A^n(nt)-\lambda^nnt]\Rightarrow\hat A$, $\tfrac{1}{\sqrt n}[S^n(nt)-\mu^nnt]\Rightarrow\hat S$, $\tfrac{1}{\sqrt n}[R(\lfloor nt\rfloor)-Pnt]\Rightarrow\hat R$, $\tfrac{1}{\sqrt n}[D^n(nt)-(1-\nu^n)nt]\Rightarrow\hat D$, where $\hat A,\hat S,\hat R,\hat D$ have continuous sample paths;
--   2. (4.6) $\sqrt n(\lambda^n-\lambda)\to c_\lambda$, $\lambda\ge0$; (4.7) $\sqrt n(\mu^n-\mu)\to c_\mu$, $\mu>0$; (5.2) $\sqrt n(\nu^n-\nu)\to c_\nu$, $0\le\nu\le1$;
--   3. (5.10) $\lambda_j+\sum_kP_{kj}\mu_k\nu_k=\mu_j\nu_j$ for each $j$, with $P$ substochastic and $P^k\to0$.
--
--   Let $\hat Z^n(t)=n^{-1/2}Z^n(nt)$, $\hat Y^n(t)=n^{-1/2}Y^n(nt)$, $\hat B^n(t)=n^{-1/2}[B^n(nt)-\nu^nnt]$ (5.11) and $\hat D^n(t)=n^{-1/2}[D^n(nt)-(1-\nu^n)nt]$. Then
--   $$
--   (\hat Z^n,\hat B^n,\hat Y^n,\hat D^n)\Rightarrow(\hat Z,\hat B,\hat Y,\hat D)\quad\text{in }D([0,\infty),\mathbb R^{4J},J_1),
--   $$
--   where $\hat Z=\phi(\hat X)$ and $\hat Y=\mathrm{diag}(\mu^{-1})\psi(\hat X)$ for the reflection map $(\psi,\phi)$ associated with $Q=P^t$, $\hat X=\hat Z(0)+\hat\xi+\hat\eta$ with
--   $$
--   \hat\xi_j(t)=\hat A_j(t)+\sum_{k=1}^J\big[\hat R_{kj}(\mu_k\nu_kt)+P_{kj}\hat S_k(\nu_kt)\big]-\hat S_j(\nu_jt),
--   $$
--   $$
--   \hat\eta_j(t)=\Big[c_{\lambda j}-(\mu_jc_{\nu j}+\nu_jc_{\mu j})+\sum_{k=1}^JP_{kj}(\mu_kc_{\nu k}+\nu_kc_{\mu k})\Big]t+\mu_j\hat D_j(t)-\sum_{k=1}^J\mu_kP_{kj}\hat D_k(t),
--   $$
--   $\hat B=-\hat D-\hat Y$, and $\hat D$ is the limit in (5.1).
--
--   This is the heavy-traffic limit for fixed (order-one) up and down times: the interruptions enter through the time changes by $\nu$ in $\hat\xi$ and through $\hat D$ and $c_\nu$ in $\hat\eta$. In the standard case of independent zero-mean Brownian primitive limits described in Remark (5.1), the netput is Brownian and $\hat Z$ is a reflected Brownian motion.
--
--   **Formalization Note** The page omits the proof ("similar to the proof of theorem 4.1"). Weak convergence, of the hypotheses and of the conclusion, is in coupling form.
--
--   Differences from the source:
--   - reading: the assumptions of section 4.1 hold with (5.1), (5.2) and (5.10) instead of (4.5) → Section 4(A) with (5.1)–(5.2) in place of (4.5) and (5.10) in place of (4.8); Σₘ u_kʲ → ∞ dropped; reason: the paper has no Section 4.1; p. 354 keeps 'all the assumptions of section 4(A) except (4.5)' and p. 356 assumes (5.10) 'instead of (4.8)'; the clause Σ u_kʲ → ∞ concerns the limits of (4.5)
--   - encoding: weak convergence in D([0, ∞), ℝ⁴ᴶ, J₁), and the joint weak convergence (4.1)–(4.4), (5.1) → CouplingConverges UocTendsto for the conclusion and CouplingConverges PrimConv5 for the hypotheses; reason: all limits are continuous, so J₁ convergence is u.o.c. convergence, and on these Polish spaces the coupling form is equivalent to weak convergence
--   - encoding: Ẑ = φ(X̂), Ŷ = diag(μ⁻¹)ψ(X̂) → any (Ẑ, Ŷ) with IsReflection Pᵗ X̂ (μŶ) Ẑ almost surely (published definition, which also allows y(0) ≥ 0); reason: the reflection is unique; the published definition agrees with (2.1)–(2.3) whenever X̂(0) ≥ 0 and extends the map by (2.4) otherwise
--   - encoding: random primitives and processes → explicit measurability of the primitives, of Zⁿ, Bⁿ at each t ≥ 0, of the limit data and of Ẑ, Ŷ; reason: needed for the laws to be defined; holds for every random network
--   - generalization: a network of J stations → J : ℕ also permits the empty network J = 0; reason: for J > 0 the full source claim is unchanged; for J = 0 all station vectors are empty and each convergence conclusion is immediate
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 356, Theorem 5.2 (assumptions pp. 347–348, 354, 356)

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Supplement_FixedUpDown

namespace ChenWhitt93.Reflection.Supplement

open MeasureTheory Filter Topology Matrix
open ChenWhitt93.JumpDiffusion

/-- Theorem 5.2 (p. 356): if the assumptions of Section 4(A) hold with (5.1), (5.2) in place of
(4.5) and (5.10) in place of (4.8), then `(Ẑⁿ, B̂ⁿ, Ŷⁿ, D̂ⁿ) ⇒ (Ẑ, B̂, Ŷ, D̂)` in
`D([0, ∞), ℝ^{4J}, J₁)`, where `Ẑ = φ(X̂)`, `Ŷ = diag(μ⁻¹)ψ(X̂)` for the reflection map `(ψ, φ)`
with `Q = Pᵗ`, `X̂ = Ẑ(0) + ξ̂ + η̂` with `ξ̂` of (5.12) and `η̂` of (5.13), `B̂ = −D̂ − Ŷ` (4.17),
and `D̂` is the limit in (5.1). `B̂ⁿ` is (5.11) and `D̂ⁿ` the left side of (5.1). All limits are
continuous, so `J₁` convergence is uniform convergence on compacts; weak convergence is written in
coupling form, for the hypotheses (4.1)–(4.4) with (5.1) (jointly) and for the conclusion. -/
theorem theorem_5_2 {J : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (Pr' : Measure Ω') [IsProbabilityMeasure Pr']
    (χ : Ω → Fin J → Fin J → ℕ → Bool) (net : ℕ → Ω → NetworkData J)
    (Z : ℕ → Ω → ℝ → Fin J → ℤ) (B : ℕ → Ω → ℝ → Fin J → ℝ)
    (lamn mun nun : ℕ → Fin J → ℝ) (lam mu nu clam cmu cnu : Fin J → ℝ)
    (P : Matrix (Fin J) (Fin J) ℝ)
    (L : Ω' → LimitData5 J) (Zh Yh : Ω' → ℝ → Fin J → ℝ)
    -- Section 3: each network's primitive data are random and satisfy the model's assumptions,
    -- and `(Zⁿ, Bⁿ)` solves (3.2)–(3.3)
    (hrand : IsRandomNetwork χ net)
    (hvalid : ∀ n, ∀ᵐ ω ∂Pr, (net n ω).IsValid (χ ω))
    (hsol : ∀ n, ∀ᵐ ω ∂Pr, IsQueueSolution (χ ω) (net n ω) (Z n ω) (B n ω))
    (hZBmeas : ∀ n t, 0 ≤ t → ∀ j,
      Measurable (fun ω => Z n ω t j) ∧ Measurable (fun ω => B n ω t j))
    -- (4.6), (4.7), (5.2), (5.10), and `P` substochastic with `Pᵏ → 0`
    (hpar : ParamHyp5 lamn mun nun lam mu nu clam cmu cnu P)
    -- (4.1)–(4.4) jointly with (5.1), with continuous limits `Â`, `Ŝ`, `R̂`, `D̂`
    (hLmeas : Measurable (fun ω' => (L ω').toPrim5))
    (hjoint : CouplingConverges PrimConv5 Pr
      (fun n ω => scaledPrimitives5 (χ ω) (net n ω) (lamn n) (mun n) (nun n) P n) Pr'
      (fun ω' => (L ω').toPrim5))
    (hreg : ∀ᵐ ω' ∂Pr', LimitRegular5 (L ω'))
    -- the limit: `(diag(μ)Ŷ, Ẑ) = (ψ(X̂), φ(X̂))`
    (hZYmeas : ∀ t, 0 ≤ t → ∀ j,
      Measurable (fun ω' => Zh ω' t j) ∧ Measurable (fun ω' => Yh ω' t j))
    (hrefl : ∀ᵐ ω' ∂Pr',
      IsReflection P.transpose (XHat5 (L ω') mu nu clam cmu cnu P) (fun t => mu * Yh ω' t)
        (Zh ω')) :
    CouplingConverges UocTendsto Pr
      (fun n ω => jointScaled5 (net n ω) (Z n ω) (B n ω) (nun n) n) Pr'
      (fun ω' => jointLimit5 (L ω') (Zh ω') (Yh ω')) := by sorry

end ChenWhitt93.Reflection.Supplement
