-- Prove2me | Theorems.Thm_BertsekasDP_piecewise_trajectory_continuation
-- name    : BertsekasDP.piecewise_trajectory_continuation
-- status  : Proved
-- author  : @davidnet
-- created : 2026-09-07T22:51:21.502173+00:00
-- url     : https://prove2.me/theorems/e1e1499e-0ebb-4828-969d-7c45b061e328
-- title:
--   Continuation to a fixed horizon from nearby initial states
-- statement:
--   Let $M$ be a fixed-horizon control model with state equation $\dot x=f(x,u)$ and terminal time $T>0$. Assume $f$ is jointly continuously differentiable. Let $(u,x)$ be admissible on $[0,T]$ from the model's initial state: $u$ takes values in $U$, its image is bounded, it is continuous off a finite set, and $x$ is continuous and solves the state equation off a finite set.
--
--   For every $\tau\in(0,T)$, there is $\delta>0$ such that every state $\xi$ with
--
--   $$\|\xi-x(\tau)\|<\delta$$
--
--   admits a continuation $z$ under the same control on the whole remaining interval:
--
--   $$z(\tau)=\xi,\qquad \dot z(t)=f(z(t),u(t))\quad(t\in[\tau,T]\setminus F_\xi),$$
--
--   where $z$ is continuous on $[\tau,T]$ and $F_\xi$ is finite. Equivalently, $(u,z)$ is admissible from $(\tau,\xi)$ up to $T$.
--
--   This is the fixed-control compact-interval specialization of openness of the domain of the solution map. It supplies the continuation of a locally constructed needle arc without imposing global Lipschitz bounds, convexity of $U$, or continuity of $u$ at the starting time.
--
--   **Formalization Note.** The control regularity is exactly bounded image and continuity away from a finite set. One-sided limits at exceptional points are not assumed. The conclusion uses a finite-exception classical solution, as obtained from the Carathéodory integral equation at continuity points of the right-hand side.
-- source:
--   Dalibor Pražák, Carathéodory theory of ODEs (fall 2024), https://www.karlin.mff.cuni.cz/~prazak/vyuka/Odr2/Skripta/en_acODR-24.pdf, Theorem 18 (open domain and continuity of the solution map), p. 8, with Theorem 13 (local uniqueness), p. 6, and Lemma 4 (integral formulation), p. 2. Fixed-control compact-interval corollary specialized to BertsekasCTModel finite-exception admissibility, not a verbatim numbered theorem. Context: D. Liberzon, Calculus of Variations and Optimal Control Theory, §4.2.4, integral formulation preceding (4.19), https://liberzon.csl.illinois.edu/teaching/cvoc/node69.html.

import Definitions.Def_BertsekasCTModel

theorem BertsekasDP.piecewise_trajectory_continuation
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 u x)
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 M.T) :
    ∃ δ > (0 : ℝ), ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖ξ - x τ‖ < δ →
      ∃ z : ℝ → EuclideanSpace ℝ (Fin n),
        BertsekasCTAdmissibleFrom M τ ξ u z := by
  sorry
