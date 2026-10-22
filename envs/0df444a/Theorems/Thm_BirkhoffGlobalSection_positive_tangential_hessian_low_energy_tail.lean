-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_tangential_hessian_low_energy_tail
-- name    : BirkhoffGlobalSection.positive_tangential_hessian_low_energy_tail
-- status  : Proved
-- author  : @caleb
-- created : 2026-10-02T21:46:40.004216+00:00
-- url     : https://prove2.me/theorems/d945fbac-1826-4f0a-8ef4-91bb7736b09e
-- title:
--   Uniform strict convexity of the Levi-Civita surface on the low-energy tail
-- statement:
--   There are $\varepsilon > 0$ and a cutoff $C$ such that, for every mass ratio and energy with
--
--   $$0 < \mu < 1, \qquad |\mu - \tfrac12| < \varepsilon, \qquad C \le c, \qquad -c < h_1(\mu),$$
--
--   the Levi-Civita Hamiltonian $K_{\mu,c}$ has positive tangential Hessian along the selected left component $\Sigma_{\mu,c}$:
--
--   $$
--   D^2K_{\mu,c}(s)(v,v) > 0\qquad\text{for all } s \in \Sigma_{\mu,c},\ v \ne 0 \text{ with } dK_{\mu,c}(s)\,v = 0,
--   $$
--
--   and $K_{\mu,c}$ is $C^2$ at each $s \in \Sigma_{\mu,c}$. Here $c = -h$, so $c \to +\infty$ is the very-negative-energy tail.
--
--   This is the uniform strict convexity of the regularized surface far down the energy tail, used in Liu–Salomão, Section 10, third paragraph.
--
--   **Why it holds.** In Levi-Civita coordinates,
--
--   $$
--   K_{\mu,c} = \tfrac12|w|^2 + c|z|^2 - \tfrac{1-\mu}{2} + 2|z|^2(z_1w_2 - z_2w_1) - \mu(z_1w_2 + z_2w_1) - \frac{\mu|z|^2}{|2z^2 - 1|}.
--   $$
--
--   On the left component, $|z|^2 = O(1/c)$ and $|w| = O(1)$. The Hessian equals $\mathrm{diag}(2c, 2c, 1, 1)$ plus a perturbation whose entries are bounded independently of $c$. The $w$-block is exactly the identity, and the mixed block is $O(1)$. By a Schur-complement estimate the full Hessian is positive definite once $c$ exceeds a constant, and so is its restriction to tangent vectors. Numerically, for $\mu \in \{0.4, 0.5, 0.6\}$, the full Hessian is already positive definite along the component for $c \ge 3$. Its least eigenvalue tends to $1$ as $c \to \infty$.
--
--   **Formalization note.** This is the analytic input of `convex_regularization_model_low_energy_tail`. With the accepted radial lemmas and `star_shaped_level_set_convex`, it makes the Levi-Civita coordinates themselves a convex regularization model on the tail.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2#S10, Section 10, third paragraph (uniform strict convexity for very negative energy). Stated as positive tangential Hessian of the Levi-Civita Hamiltonian on the selected left component, in the sense of HasPositiveTangentialHessianOn (Joung--van Koert, https://arxiv.org/html/2407.19159v3, Proposition 4.4 convention).

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Uniform strict convexity of the Levi-Civita component on the very-negative-energy
tail: for mass ratios near one half and all sufficiently large `c`, the Levi-Civita
Hamiltonian has positive tangential Hessian along the selected left component. -/
theorem positive_tangential_hessian_low_energy_tail :
    ∃ ε C : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → C ≤ c → belowFirstCriticalValue μ c →
        HasPositiveTangentialHessianOn (leviCivitaHamiltonian μ c)
          (leftEnergyComponent μ c) := by sorry

end BirkhoffGlobalSection
