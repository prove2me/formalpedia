-- Prove2me | Theorems.Thm_BoydADMM_Consensus_sharing_z_update_reduction
-- name    : BoydADMM.Consensus.sharing_z_update_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:07:11.932844+00:00
-- url     : https://prove2.me/theorems/03efa5da-39ba-4d78-965e-5b0835f4f68f
-- title:
--   §7.3 (goal): the sharing $z$-update reduces to one $n$-variable problem plus (7.13), and the dual variables agree (7.14)
-- statement:
--   Let $N\ge1$, $\rho>0$ and let $g:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be the shared objective of the sharing problem (7.11)–(7.12).
--
--   1. **Reduction of the $z$-update.** For any $a_1,\dots,a_N\in\mathbb R^n$ (in ADMM, $a_i=u_i^k+x_i^{k+1}$), a tuple $(z_1,\dots,z_N)$ minimizes the $Nn$-variable problem
--   $$g\Big(\sum_{i=1}^N z_i\Big)+(\rho/2)\sum_{i=1}^N\|z_i-a_i\|_2^2$$
--   if and only if its average $\bar z=\frac1N\sum_i z_i$ minimizes the $n$-variable problem
--   $$g(N\bar z)+(\rho/2)\sum_{i=1}^N\|\bar z-\bar a\|_2^2$$
--   and $z_i=a_i+\bar z-\bar a$ for every $i$ (7.13).
--
--   2. **The dual variables agree (7.14).** Along every run $x_i^k, z_i^k, u_i^k$ of the scaled sharing ADMM (p. 56), for every $k\ge0$ and every $i$,
--   $$u_i^{k+1}=\bar u^k+\bar x^{k+1}-\bar z^{k+1}.$$
--   In particular all $u_i^{k+1}$ are equal, so a single dual variable suffices.
--
--   This is what makes sharing ADMM practical: the $z$-update needs only the averages $\bar x^{k+1}$, $\bar u^k$ and one problem in $n$ variables.
--
--   **Formalization Note** Each extended-real-valued function $\varphi:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ of the book is encoded by its effective domain $\operatorname{dom}\varphi$ (a set) and its finite values on it (a real function); a minimization of a sum containing $\varphi$ is a minimization over $\operatorname{dom}\varphi$. The $Nn$-variable problem is minimized over tuples with $\sum_i z_i\in\operatorname{dom}g$ and the $n$-variable one over $\bar z$ with $N\bar z\in\operatorname{dom}g$. The book states only that the $z$-update "can be computed by" solving the reduced problem and applying (7.13); the equivalence stated here contains that direction and its converse. No convexity of $f_i$ or $g$ is needed. The book's "$u\in\mathbf R^m$" refers to a vector of $\mathbb R^n$. (7.14) is derived for every run, not built into the definition of the run.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 57, §7.3 (reduction of the z-update to one n-variable problem, (7.13), (7.14))

import Mathlib
import Definitions.Def_BoydADMM_Consensus_Model

open scoped BigOperators InnerProductSpace

namespace BoydADMM.Consensus

/-- §7.3, p. 57 (goal). Let `g` have effective domain `Cg`, `ρ > 0`, `N ≥ 1`.

(1) For any `a_1, …, a_N ∈ ℝⁿ`, `(z_1, …, z_N)` solves the sharing `z`-update
`minimize g(∑_i z_i) + (ρ/2)∑_i ‖z_i − a_i‖²` (over `∑_i z_i ∈ dom g`) iff its average `z̄` solves
the `n`-variable problem `minimize g(N z̄) + (ρ/2)∑_{i=1}^N ‖z̄ − ā‖²` (over `N z̄ ∈ dom g`) and
`z_i = a_i + z̄ − ā` for every `i` (7.13).

(2) Along every run of sharing ADMM, (7.14) holds: `u_i^{k+1} = ū^k + x̄^{k+1} − z̄^{k+1}` for every
`k` and `i`; in particular all `u_i^{k+1}` are equal. -/
theorem sharing_z_update_reduction {n N : ℕ} (hN : 0 < N) (ρ : ℝ) (hρ : 0 < ρ)
    (Cg : Set (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∀ a z : Fin N → EuclideanSpace ℝ (Fin n),
      ((∑ i, z i) ∈ Cg ∧ ∀ z' : Fin N → EuclideanSpace ℝ (Fin n), (∑ i, z' i) ∈ Cg →
          sharingZObj g ρ a z ≤ sharingZObj g ρ a z') ↔
        ((N : ℝ) • avg z ∈ Cg ∧
          (∀ w : EuclideanSpace ℝ (Fin n), (N : ℝ) • w ∈ Cg →
            g ((N : ℝ) • avg z) + (ρ / 2) * ∑ _i : Fin N, ‖avg z - avg a‖ ^ 2 ≤
              g ((N : ℝ) • w) + (ρ / 2) * ∑ _i : Fin N, ‖w - avg a‖ ^ 2) ∧
          ∀ i, z i = a i + avg z - avg a)) ∧
    (∀ (Cf : Fin N → Set (EuclideanSpace ℝ (Fin n))) (f : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
      (x z u : ℕ → Fin N → EuclideanSpace ℝ (Fin n)),
      IsSharingADMMRun Cf f Cg g ρ x z u →
        ∀ k i, u (k + 1) i = avg (u k) + avg (x (k + 1)) - avg (z (k + 1))) := by sorry

end BoydADMM.Consensus
