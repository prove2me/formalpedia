-- Prove2me | Theorems.Thm_BoydADMM_Prox_prox_nonnegOrthant
-- name    : BoydADMM.Prox.prox_nonnegOrthant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:32.085173+00:00
-- url     : https://prove2.me/theorems/f7f74636-0407-4812-b918-779dc5916b69
-- title:
--   §4.1, p. 26 — the prox of the indicator of ℝⁿ₊ is (v)₊
-- statement:
--   Let $\rho>0$, $v\in\mathbb R^n$, and let $f$ be the indicator function of the nonnegative orthant $\mathbf R^n_+=\{x\mid x_i\ge0\text{ for all }i\}$. Then the $x$-update
--   $$x^+=\operatorname*{argmin}_x\Bigl(f(x)+\tfrac{\rho}{2}\|x-v\|_2^2\Bigr)$$
--   is unique and equals the nonnegative part of $v$:
--   $$x^+=(v)_+,\qquad ((v)_+)_i=\max(v_i,0).$$
--   That is, a vector $x$ minimizes $\tfrac{\rho}{2}\|x-v\|_2^2$ over $\mathbf R^n_+$ if and only if $x=(v)_+$.
--
--   This is the simplest example of a projection-type ADMM update; it appears in nonnegative least squares and in every problem with sign constraints.
--
--   **Formalization Note** The indicator of $\mathbf R^n_+$ is encoded as the domain $\mathbf R^n_+$ with the zero function; $(v)_+$ is the vector of componentwise maxima with $0$.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 26, §4.1

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem prox_nonnegOrthant {n : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (v : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    IsProx (nonnegOrthant n) (fun _ => 0) ρ v x ↔ x = posPartVec v := by sorry

end BoydADMM.Prox
