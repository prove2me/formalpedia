-- Prove2me | Theorems.Thm_BordenaveCollins_tendsto_re_trTau_pow_rpow
-- name    : BordenaveCollins.tendsto_re_trTau_pow_rpow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:09:19.225212+00:00
-- url     : https://prove2.me/theorems/86fc9afb-cff2-4d22-adb5-af99d9016ffd
-- title:
--   The moments of x*x under the trace of M_D(ℂ) ⊗ ℂ[F_r * Γ_s] recover the reduced norm
-- statement:
--   Let $D \ge 1$ and $x \in M_D(\mathbb C) \otimes \mathbb C[F_r * \Gamma_s]$, and let $\tau_D(y) = \frac1D \operatorname{tr}(y_e)$ be the normalized trace of the coefficient of the identity. Then
--   $$\Big(\operatorname{Re} \tau_D\big((x^* x)^p\big)\Big)^{1/(2p)} \longrightarrow \|x\| \qquad (p \to \infty),$$
--   where $x^* = \sum_g x_g^*\, g^{-1}$ and $\|x\|$ is the norm of $x$ in the left-regular representation, acting on $D$ copies of $\ell^2(F_r * \Gamma_s)$.
--
--   This expresses the faithfulness of the canonical trace on the reduced group C*-algebra; it is the input of the lower bound in Appendix A of Chen, Garza-Vargas, Tropp and van Handel, *A new approach to strong convergence*, here for $F_r * \Gamma_s$.
--
--   **Formalization note.** The definitions (`MG`, `adj`, `trTau`, `regOp`) are in the bundle `Def_BordenaveCollins`. The power is Lean's real power applied to the real part of the trace.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 32-33, the faithfulness of the trace behind the lower bounds of Appendix A, for F_r * Γ_s; a step of our proof of the theorem of Bordenave, C. and Collins, B., Eigenvalues of random lifts and polynomials of random permutation matrices, Ann. of Math. (2) 190 (2019) 811–875, https://doi.org/10.4007/annals.2019.190.3.3

import Mathlib
import Definitions.Def_BordenaveCollins

open Filter Topology

namespace BordenaveCollins

theorem tendsto_re_trTau_pow_rpow {r s : ℕ} {D : ℕ} (hD : 1 ≤ D) (x : MG D r s) :
    Tendsto (fun p : ℕ => ((trTau ((adj x * x) ^ p)).re) ^ (1 / (2 * (p : ℝ)))) atTop
      (𝓝 ‖regOp x‖) := by
  sorry

end BordenaveCollins
