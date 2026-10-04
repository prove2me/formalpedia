-- Prove2me | Theorems.Thm_DemandResponse_SecondBest_propA4_ii_minimiser
-- name    : DemandResponse.SecondBest.propA4_ii_minimiser
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:42:28.714564+00:00
-- url     : https://prove2.me/theorems/5db39fb3-6e68-4605-b71e-52773cdfbbde
-- title:
--   Proposition A.4 (ii) — the optimal payment rate $z_{SB}$ lies in $[v_x,\frac p{r+p}v_x]$ for $v_x\le0$ and equals $\frac p{r+p}v_x$ for $v_x\ge0$
-- statement:
--   Fix real numbers $y$ (standing for $v_x$) and $k$ (standing for $v_{xx}$), and consider the objective of the producer's HJB equation (A.11) in the limit $A\nearrow\infty$:
--   $$\Phi(z):=F_0\big(h-k+rz^2+p(z-y)^2\big)+\bar\mu\,(z^-+y)^2,\qquad z\in\mathbb R,$$
--   where $F_0$ is the function of Lemma A.1. Then:
--
--   1. if $y\ge0$, the point $z=\frac p{r+p}y$ minimises $\Phi$ over $\mathbb R$;
--   2. if $y\le0$, $\Phi$ has a minimiser over $\mathbb R$ in the interval $\big[y,\frac p{r+p}y\big]$.
--
--   This locates the second-best payment rate for consumption reduction: in off-peak periods it is explicit, and in peak periods it lies between the producer's marginal value $v_x$ and its fraction $\frac p{r+p}v_x$.
--
--   **Formalization Note.** The page states the claim "for large $A$", with the cap term $\eta_A(v_x,z)=(v_x+(z^--A)^+)^2-v_x^2\to0$ as $A\nearrow\infty$ in (A.11); it is formalized with $\eta_A\equiv0$, the limit the page names (with $\eta_A$ at finite $A$ the claim can fail). The page's open interval $(v_x,\frac p{r+p}v_x)$ is empty at $v_x=0$, where the minimiser is $0$; the closed interval is used. "The minimiser" is read as "a minimiser": when $\bar\mu=0$ and $d=0$ the minimiser need not be unique.
-- source:
--   arXiv:1810.09063v3, Appendix A.3, Proposition A.4 (ii) and (A.11) (p. 30)

import Mathlib
import Definitions.Def_DemandResponse_SecondBest_Hamiltonian

namespace DemandResponse.SecondBest

/-- Proposition A.4 (ii), minimiser claim (arXiv:1810.09063v3, p. 30), read in the limit `A ↗ ∞`
(`η_A ≡ 0`) and with the closed interval `[v_x, p v_x / (r+p)]`. Here `y` stands for `v_x` and `k` for
`v_xx`; the objective of (A.11) is `z ↦ F₀(h - k + r z² + p (z - y)²) + μ̄ (z⁻ + y)²`. -/
theorem propA4_ii_minimiser {N d : ℕ} (P : Params N d) (y k : ℝ) :
    let Φ : ℝ → ℝ := fun z =>
      F0 P (P.h - k + P.r * z ^ 2 + P.p * (z - y) ^ 2) + muBar P * (negp z + y) ^ 2
    (0 ≤ y → IsMinOn Φ Set.univ (P.p / (P.r + P.p) * y)) ∧
    (y ≤ 0 → ∃ z ∈ Set.Icc y (P.p / (P.r + P.p) * y), IsMinOn Φ Set.univ z) := by sorry

end DemandResponse.SecondBest
