-- Prove2me | Theorems.Thm_DirectFidelity_RandomState_eq_35
-- name    : DirectFidelity.RandomState.eq_35
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:46.716768+00:00
-- url     : https://prove2.me/theorems/ccf2245d-8874-41c8-a7a3-56817ca12b44
-- title:
--   (35), p. 7 — Pr[(31) fails for some i] ≤ 4 exp(cd log 2 − C₁dε²) = 4 exp(−cd log 2) = 4·2^{−cd}
-- statement:
--   Let $n \ge 0$, $d = 2^n$, $c > 0$, and let $\varphi_1,\dots,\varphi_s \in \mathbb C^d$ be unit vectors with $s \le 2^{cd}$. Put $\varepsilon = \sqrt{9\pi^3(\log 2)c}$ and $C_1 = 2/(9\pi^3)$. If $\psi$ is uniformly distributed on the unit sphere of $\mathbb C^d$, then
--   $$\Pr\bigl[\exists i:\ |\langle\varphi_i|\psi\rangle| > \varepsilon\bigr] \le 4\exp\bigl(cd(\log 2) - C_1 d\varepsilon^2\bigr) = 4\exp\bigl(-cd(\log 2)\bigr) = 4\cdot 2^{-cd}.$$
--
--   The event on the left is "condition (31) of Lemma 1 fails for some $i$". The bound is the union bound over the $s \le 2^{cd}$ events of (34).
--
--   **Formalization Note** "(31) fails" is the strict inequality $|\langle\varphi_i|\psi\rangle| > \varepsilon$, the negation of (31). The two equalities of the printed chain are part of the statement; they hold because $C_1\varepsilon^2 = 2c\log 2$. The hypothesis $c > 0$ is the reading of "c is some constant" under which $\varepsilon$ is defined.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, p. 7, eq. (35)

import Mathlib
import Definitions.Def_DirectFidelity_RandomState_Setting

namespace DirectFidelity.RandomState

open MeasureTheory

theorem eq_35 (n : ℕ) (c : ℝ) (hc : 0 < c) (s : ℕ)
    (hs : (s : ℝ) ≤ (2 : ℝ) ^ (c * DirectFidelity.State.dim n)) (φ : Fin s → E n) (hφ : ∀ i, ‖φ i‖ = 1) :
    (unifSphere n).real {ψ | ∃ i, epsC c < ‖inner ℂ (φ i) (ψ : E n)‖} ≤
        4 * Real.exp (c * DirectFidelity.State.dim n * Real.log 2 - C1 * DirectFidelity.State.dim n * epsC c ^ 2) ∧
      4 * Real.exp (c * DirectFidelity.State.dim n * Real.log 2 - C1 * DirectFidelity.State.dim n * epsC c ^ 2) =
        4 * Real.exp (-(c * DirectFidelity.State.dim n * Real.log 2)) ∧
      4 * Real.exp (-(c * DirectFidelity.State.dim n * Real.log 2)) = 4 * (2 : ℝ) ^ (-(c * DirectFidelity.State.dim n)) := by sorry
end DirectFidelity.RandomState
