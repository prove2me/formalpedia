-- Prove2me | Theorems.Thm_Arxiv0812_1178_wrapped_kernel_closure
-- name    : Arxiv0812_1178.wrapped_kernel_closure
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T08:50:04.989972+00:00
-- url     : https://prove2.me/theorems/3a924f6a-2e36-451f-b431-be60d44ef5bd
-- title:
--   Appendix C, eqs. (45)-(47): the $2\pi$-wrapped kernel of $C$ is $\bar B\alpha$ modulo $2\pi$
-- statement:
--   Let $N_t\ge3$ and let $\bar B$ be the baseline operator $B$ with its first column removed. Then:
--
--   1. $\operatorname{im}B=\operatorname{im}\bar B$, so $\ker C=\operatorname{im}\bar B$ (eq. (45)).
--   2. If $\phi^{ker}\in\mathbb R^{N_b}$ satisfies $C\phi^{ker}\equiv0\pmod{2\pi}$, that is, $C\phi^{ker}=2\pi k$ for some integer vector $k$, then there are $\alpha\in\mathbb R^{N_t-1}$ and an integer vector $\kappa$ with
--   $$\phi^{ker}=\bar B\alpha+2\pi\kappa,$$
--   that is, $\phi^{ker}\equiv\bar B\alpha\pmod{2\pi}$ (eq. (47)).
--
--   **Formalization Note** The sentence in Sec. 3.B is printed with the hypothesis "$\phi^{ker}=0\ [2\pi]$". The hypothesis used and proved in Appendix C, and stated here, is $C\phi^{ker}\equiv0\ [2\pi]$.
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), claim c004; Sec. 3.B, paragraph before eq. (27), PDF p. 9; proof in Appendix C, eqs. (45)-(47), PDF pp. 18-19

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv0812_1178

theorem wrapped_kernel_closure {n : ℕ} (hn : 3 ≤ n) :
    LinearMap.range (baselineOp n).mulVecLin = LinearMap.range (baselineOpBar n).mulVecLin ∧
    LinearMap.ker (closureOp n).mulVecLin = LinearMap.range (baselineOpBar n).mulVecLin ∧
    ∀ φker : Baseline n → ℝ,
      (∃ k : ClosureIdx n → ℤ, closureOp n *ᵥ φker = fun c => 2 * Real.pi * k c) →
      ∃ (α : Fin (n - 1) → ℝ) (κ : Baseline n → ℤ),
        φker = baselineOpBar n *ᵥ α + fun b => 2 * Real.pi * κ b := by sorry

end Arxiv0812_1178
