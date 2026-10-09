-- Prove2me | Theorems.Thm_CompositeLB_DetSC_final_count
-- name    : CompositeLB.DetSC.final_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:25:18.111783+00:00
-- url     : https://prove2.me/theorems/b06e6217-7de6-423b-bab8-598184fa0215
-- title:
--   Appendix B.4, p. 18 — the explicit m/(40√λ) query count
-- statement:
--   Let $m\ge2$, $0<\lambda<1/73$, $\epsilon>0$, and $\epsilon_0>3\epsilon/\lambda$. Put $Q=(\lfloor m/2\rfloor/m)(1/\lambda-1)+1$. The paper's arithmetic lower bound is
--
--   $$\frac m2\left\lfloor\frac{\sqrt Q-1}{4}\log\!\left(\frac{\epsilon_0}{2\sqrt Q\,\epsilon}\right)\right\rfloor\ge\frac{m}{40\sqrt\lambda}\log\!\left(\frac{\epsilon_0}{2\sqrt Q\,\epsilon}\right)\ge\frac{m}{40\sqrt\lambda}\log\!\left(\frac{\sqrt\lambda\,\epsilon_0}{2\epsilon}\right).$$
--
--   This is the explicit normalized count behind the asymptotic lower bound in Theorem 4.
--
--   **Formalization Note** The floor is Nat.floor, and m / 2 inside $Q$ is floored by natural-number division. The parameter hypotheses make the logarithm and the floor's argument positive.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.4, p. 18, final display

import Mathlib
import Definitions.Def_CompositeLB_DetSC_HardInstance

namespace CompositeLB.DetSC

/-- Appendix B.4, p. 18: the printed explicit count in terms of `m`, λ, ε, and ε₀. -/
theorem final_count (m : ℕ) (hm : 2 ≤ m)
    (lam eps eps0 Q : ℝ)
    (hlam : 0 < lam) (hlam73 : lam < 1 / 73)
    (heps : 0 < eps) (heps0 : 3 * eps / lam < eps0)
    (hQ : Q = bigQ m lam) :
    (m : ℝ) / 2 *
        (Nat.floor ((Real.sqrt Q - 1) / 4 *
          Real.log (eps0 / (2 * Real.sqrt Q * eps))) : ℝ) ≥
      (m : ℝ) / (40 * Real.sqrt lam) *
        Real.log (eps0 / (2 * Real.sqrt Q * eps)) ∧
    (m : ℝ) / (40 * Real.sqrt lam) *
        Real.log (eps0 / (2 * Real.sqrt Q * eps)) ≥
      (m : ℝ) / (40 * Real.sqrt lam) *
        Real.log (Real.sqrt lam * eps0 / (2 * eps)) := by sorry

end CompositeLB.DetSC
