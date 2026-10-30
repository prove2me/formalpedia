-- Prove2me | Theorems.Thm_ExactPenGNEP_NonShared_theorem_11_b
-- name    : ExactPenGNEP.NonShared.theorem_11_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:38.743103+00:00
-- url     : https://prove2.me/theorems/4958e835-31bf-4e1f-8cf3-c41484387769
-- title:
--   Theorem 11 (b), pp. 17–18 — under the Slater-type condition, for all large ρ every equilibrium of the ℓq-penalized NEP is an equilibrium of the GNEP
-- statement:
--   Consider a GNEP $(C, X; \theta)$ with $N$ players in which:
--
--   1. each private set $C^\nu \subseteq \mathbb R^{n_\nu}$ is compact and convex;
--   2. each coupled set is finitely representable as in (16), $X^\nu(x^{-\nu}) = \{x^\nu \mid g^\nu(x^\nu, x^{-\nu}) \le 0,\ h^\nu(x) = 0\}$, with $h^\nu$ affine and each $g^\nu_j(\cdot, x^{-\nu})$ convex and differentiable for all $x^{-\nu} \in C^{-\nu}$;
--   3. each $\theta_\nu(\cdot, x^{-\nu})$ is convex and Lipschitz continuous on $C^\nu$ with a common constant $\mathrm{Lip}_\theta > 0$, for all $x^{-\nu} \in C^{-\nu}$;
--   4. $q \in (1, \infty)$, and $r_{\nu;q}$ is the $\ell_q$ residual (17) of $X^\nu(x^{-\nu})$.
--
--   Suppose there exists $\alpha > 0$ such that for every $x \in C$ not in the graph of $X$ there exist $\hat x \in C$ and a player $\hat\nu$ with $x^{\hat\nu} \notin X^{\hat\nu}(x^{-\hat\nu})$ such that $\nabla_{x^{\hat\nu}} g^{\hat\nu}_i(x)^T(\hat x^{\hat\nu} - x^{\hat\nu}) \le -\alpha$ whenever $g^{\hat\nu}_i(x) > 0$, and $[\operatorname{sgn} h^{\hat\nu}_j(x)]\, \nabla_{x^{\hat\nu}} h^{\hat\nu}_j(x)^T(\hat x^{\hat\nu} - x^{\hat\nu}) \le -\alpha$ whenever $h^{\hat\nu}_j(x) \ne 0$. Then there is $\bar\rho > 0$ such that
--
--   $$\forall \rho > \bar\rho:\quad x^* \text{ equilibrium of the NEP } (C; \theta + \rho\, r_{X;q}) \implies x^* \text{ equilibrium of the GNEP } (C, X; \theta).$$
--
--   In the penalized NEP each player $\nu$ minimizes $\theta_\nu(x^\nu, x^{-\nu}) + \rho\, r_{\nu;q}(x^\nu, x^{-\nu})$ over $x^\nu \in C^\nu$ alone: the coupled constraints, including equality constraints, are moved into the objective with a single penalty parameter for all players.
--
--   **Formalization Note** "For all $x^{-\nu} \in C^{-\nu}$" quantifies over profiles whose rival blocks lie in their private sets, with the own block free. $\bar\rho$ is chosen after the data and before $\rho$ and the equilibrium. The Slater-type hypothesis is bundled as `SlaterTypeCQ`; it is required only at points of $C$ outside the graph of $X$. Part (a) of Theorem 11 (existence of penalized equilibria) is not formalized. With $N = 0$ or with no constraints the statement holds trivially, as on the page; no nondegeneracy is printed.
-- source:
--   Ba & Pang, Exact penalization of generalized Nash equilibrium problems, arXiv:1811.10674v2, pp. 17–18, Theorem 11 (b)

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting

open LeiBR.Sync

namespace ExactPenGNEP.NonShared

theorem theorem_11_b {N : ℕ} {n m p : Fin N → ℕ} (C : ∀ ν, Set (Strat n ν))
    (g : ∀ ν, Fin (m ν) → Profile n → ℝ) (h : ∀ ν, Fin (p ν) → Profile n →ᵃ[ℝ] ℝ)
    (θ : Fin N → Profile n → ℝ) (Lip q : ℝ)
    (hCc : ∀ ν, IsCompact (C ν)) (hCv : ∀ ν, Convex ℝ (C ν))
    (hg_cvx : ∀ ν i (x : Profile n), (∀ ν' ≠ ν, x ν' ∈ C ν') →
      ConvexOn ℝ Set.univ (fun y => g ν i (Function.update x ν y)))
    (hg_diff : ∀ ν i (x : Profile n), (∀ ν' ≠ ν, x ν' ∈ C ν') →
      Differentiable ℝ (fun y => g ν i (Function.update x ν y)))
    (hLip : 0 < Lip)
    (hθ_cvx : ∀ ν (x : Profile n), (∀ ν' ≠ ν, x ν' ∈ C ν') →
      ConvexOn ℝ (C ν) (fun y => θ ν (Function.update x ν y)))
    (hθ_lip : ∀ ν (x : Profile n), (∀ ν' ≠ ν, x ν' ∈ C ν') →
      LipschitzOnWith (Real.toNNReal Lip) (fun y => θ ν (Function.update x ν y)) (C ν))
    (hq : 1 < q)
    (hb : SlaterTypeCQ C g h) :
    ∃ ρbar > (0 : ℝ), ∀ ρ > ρbar, ∀ x : Profile n,
      IsNashEq C (fun ν y => θ ν y + ρ * lqRes (g ν) (fun j z => h ν j z) q y) x →
        IsGNE C (frSet g h) θ x := by sorry

end ExactPenGNEP.NonShared
