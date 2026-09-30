-- Prove2me | Theorems.Thm_ChitourPrescribedTime_FixedTime_lemma31_coordinate_bound
-- name    : ChitourPrescribedTime.FixedTime.lemma31_coordinate_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:08:15.495991+00:00
-- url     : https://prove2.me/theorems/a9841ba7-939a-44dd-a144-5f90199ff5af
-- title:
--   Lemma 31 — uniform bound on $x_j$ and $v_j$ on the shell $B^\kappa_{1-m,1+m}$
-- statement:
--   Let $n\ge1$, gains $\ell_1,\dots,\ell_n>0$ and $m\in(0,1)$. Then there is a constant $X_n>0$, depending only on $m$ and the gains, such that for every $\kappa\in[-\tfrac1{2n},\tfrac1{2n}]$ and every $x$ in the shell
--   $$B^\kappa_{1-m,1+m}=\{x\in\mathbb R^n\mid 1-m\le V_\kappa(x)\le 1+m\},$$
--   one has $|x_j|\le X_n$ for $1\le j\le n$ and $|v_j(x)|\le X_n$ for $0\le j\le n$.
--
--   The bound is the compactness input for the perturbation estimates of Lemma 32.
--
--   **Formalization Note** The paper calls $X_n$ "explicit"; the statement asserts existence only. The constant is quantified before $\kappa$ and $x$. The coordinate $x_0$ does not exist, so the coordinate bound is for $1\le j\le n$ (`i : Fin n`), while the bound on $v_j$ is for $0\le j\le n$.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1038, Lemma 31

import Mathlib
import Definitions.Def_ChitourPrescribedTime_FixedTime_Stability
import Definitions.Def_ChitourPrescribedTime_FixedTime_PureChain
import Definitions.Def_ChitourPrescribedTime_FixedTime_Feedback
import Definitions.Def_ChitourPrescribedTime_FixedTime_Lyapunov

namespace ChitourPrescribedTime.FixedTime

/-- Lemma 31 (p. 1038): on `B^κ_{1-m,1+m}`, uniformly in `κ ∈ [-1/(2n), 1/(2n)]`, the
coordinates `x_j` (`1 ≤ j ≤ n`) and the virtual controls `v_j` (`0 ≤ j ≤ n`) are bounded by
one constant `X_n` depending only on `m` and the gains. -/
theorem lemma31_coordinate_bound (n : ℕ) (hn : 1 ≤ n) (ℓ : Fin n → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (m : ℝ) (hm : m ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ X : ℝ, 0 < X ∧
      ∀ κ ∈ Set.Icc (-(1 / (2 * (n : ℝ)))) (1 / (2 * (n : ℝ))),
        ∀ x : EuclideanSpace ℝ (Fin n), 1 - m ≤ lyapV ℓ κ x → lyapV ℓ κ x ≤ 1 + m →
          (∀ i : Fin n, |x i| ≤ X) ∧ ∀ j : ℕ, j ≤ n → |vSeq ℓ κ x j| ≤ X := by sorry

end ChitourPrescribedTime.FixedTime
