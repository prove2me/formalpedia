-- Prove2me | Theorems.Thm_Arxiv2608_05214_glm_equation
-- name    : Arxiv2608_05214.glm_equation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:16:49.163943+00:00
-- url     : https://prove2.me/theorems/cd657b5f-6d3c-499f-9b62-0f838bb66cf2
-- title:
--   Eq. (27): the Gelfand–Levitan–Marchenko equation
-- statement:
--   Let $q:\mathbb R\to\mathbb R$ be smooth and zero outside $[0,\tau_{\max}]$. Let $R$ be the reflection response of the 1D Schrödinger equation $\partial_t^2\psi-\partial_\tau^2\psi+q(\tau)\psi=0$, recorded at $\tau=0$, for a unit impulse incident from the left. That is, $\psi=\delta(t-\tau)+g(\tau,t)H(t-\tau)$ solves the equation on $\mathbb R^2$ with $g$ of class $C^2$ on $\{t\ge\tau\}$, the tail equals the reflected wave, $g(\tau,t)=R(t+\tau)$ for $\tau<0\le t-\tau$, and $R(t)=0$ for $t<0$ (so on $\tau<0$, $\psi=\delta(t-\tau)+R(t+\tau)$ for all $t$). Let $A(\tau,t)$ be the annihilator kernel: $A$ is $C^2$ on the cone $|t|\le\tau$, $\psi_a=\delta(t-\tau)+A(\tau,t)\mathbf 1_{|t|<\tau}$ solves the same equation on $\tau>0$, and $A(\tau,-\tau)=0$. Then for every $\tau>0$ and every $|t|<\tau$,
--
--   $$A(\tau,t)+R(t+\tau)+\int_{-\tau}^{\tau}A(\tau,s)\,R(s+t)\,ds=0.$$
--
--   This is the Gelfand–Levitan–Marchenko equation: for each depth $\tau$ it is a Fredholm integral equation of the second kind for $A(\tau,\cdot)$, whose only input is the measured reflection response.
--
--   **Formalization Note** Solutions containing the pulse $\delta(t-\tau)$ are understood in the weak sense, tested against smooth compactly supported functions. The kernel $A$ is characterised by eqs. (24), (A-6) and (A-7), with $A=0$ on $t=-\tau$. The paper's diagonal relation (25)/(A-8) is not used: its printed sign is inconsistent with (24) and (17), and the kernel defined here satisfies $A(\tau,\tau)=+\frac12\int_0^\tau q$.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), claim c005; Section III-D (Derivation of the GLM Equation), eq. (27), PDF p. 7; Appendix A-C, eq. (A-11), PDF p. 31

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Arxiv2608_05214

theorem glm_equation (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q) (τmax : ℝ)
    (hsupp : Function.support q ⊆ Set.Icc 0 τmax)
    (R : ℝ → ℝ) (hR : IsReflectionResponse q R)
    (A : ℝ × ℝ → ℝ) (hA : IsAnnihilatorKernel q A) :
    ∀ τ t : ℝ, 0 < τ → |t| < τ →
      A (τ, t) + R (t + τ) + (∫ s in (-τ)..τ, A (τ, s) * R (s + t)) = 0 := by sorry

end Arxiv2608_05214
