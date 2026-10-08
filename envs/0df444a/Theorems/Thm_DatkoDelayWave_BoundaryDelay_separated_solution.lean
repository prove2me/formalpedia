-- Prove2me | Theorems.Thm_DatkoDelayWave_BoundaryDelay_separated_solution
-- name    : DatkoDelayWave.BoundaryDelay.separated_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:58:55.825994+00:00
-- url     : https://prove2.me/theorems/41b5380a-2965-439f-9690-d2007127f22d
-- title:
--   Separated solutions — an eigenpair (ω, φ) gives the solution u = e^{ωt}φ(x) of (1), (2), (8)
-- statement:
--   Let $a, k, \varepsilon$ be real, $\omega \in \mathbb C$, and let $\varphi : \mathbb R \to \mathbb C$ be a $C^2$ function with
--   $$
--   \varphi''(x) = (a+\omega)^2\varphi(x)\ (0<x<1),\qquad \varphi(0) = 0,\qquad \varphi'(1) + k\omega e^{-\varepsilon\omega}\varphi(1) = 0 .
--   $$
--   Then
--   $$
--   u(x,t) = e^{\omega t}\varphi(x)
--   $$
--   is a classical solution of the delayed system (1), (2), (8): it is $C^2$ on $\mathbb R^2$, solves $u_{tt} - u_{xx} + 2au_t + a^2u = 0$ for $0<x<1$, $t>0$, vanishes at $x = 0$, and satisfies $u_x(1,t) = -k u_t(1,t-\varepsilon)$ for $t > \varepsilon$.
--
--   This is the sense in which "the spectrum can be exhibited by setting $u = e^{\omega t}\varphi(x)$": each spectral point $\omega$ carries a solution growing or decaying like $e^{(\operatorname{Re}\omega) t}$.
-- source:
--   Datko, Lagnese, Polis, An example on the effect of time delays in boundary feedback stabilization of wave equations, SIAM J. Control Optim. 24 (1986), p. 153, the ansatz u = e^{ωt}φ(x) before Eq. (5), with the boundary condition of the proof of the Theorem (p. 154)

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

namespace DatkoDelayWave.BoundaryDelay

theorem separated_solution (a k ε : ℝ) (ω : ℂ) (φ : ℝ → ℂ)
    (hφ : IsEigenpair a k ε ω φ) :
    IsClassicalSolution a k ε (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) := by sorry

end DatkoDelayWave.BoundaryDelay
