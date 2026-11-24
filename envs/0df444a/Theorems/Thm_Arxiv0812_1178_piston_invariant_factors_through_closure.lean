-- Prove2me | Theorems.Thm_Arxiv0812_1178_piston_invariant_factors_through_closure
-- name    : Arxiv0812_1178.piston_invariant_factors_through_closure
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:49:02.407437+00:00
-- url     : https://prove2.me/theorems/6fe14141-13d4-4d0c-89ce-c7e62661069d
-- title:
--   Sec. 2.C, eq. (11): piston-invariant functions factor through the closure operator
-- statement:
--   Let $N_t\ge3$ and let $f$ be a continuously differentiable function of the vector $\phi\in\mathbb R^{N_b}$ of baseline phases, with values in a real normed space (for instance $\mathbb R$ or $\mathbb C$). Suppose $f$ is piston-invariant (eq. (8)):
--   $$f(\phi+B\varpi)=f(\phi)\quad\text{for all }\phi\in\mathbb R^{N_b},\ \varpi\in\mathbb R^{N_t}.$$
--   Then there is a continuously differentiable function $g$ on $\mathbb R^{(N_t-1)(N_t-2)/2}$ such that
--   $$f(\phi)=g(C\phi)\quad\text{for all }\phi.$$
--
--   In words, every turbulence-free observable of the short-exposure phases is a function of the closure phases.
--
--   **Formalization Note** As in the paper's proof (Appendix B), phases are unwrapped real vectors. The paper does not state the codomain of $f$. A general real normed space is used here, which covers real-valued and complex-valued (bispectrum) observables.
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), claim c002; Sec. 2.C, second property, eq. (11), PDF p. 5; proof in Appendix B, eq. (44), PDF p. 18

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv0812_1178

theorem piston_invariant_factors_through_closure {n : ℕ} (hn : 3 ≤ n) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (Baseline n → ℝ) → E) (hf : ContDiff ℝ 1 f)
    (hpiston : ∀ (φ : Baseline n → ℝ) (varpi : Fin n → ℝ), f (φ + baselineOp n *ᵥ varpi) = f φ) :
    ∃ g : (ClosureIdx n → ℝ) → E, ContDiff ℝ 1 g ∧ ∀ φ, f φ = g (closureOp n *ᵥ φ) := by sorry

end Arxiv0812_1178
