-- Prove2me | Theorems.Thm_DataDrivenRO_Moment_theorem_10
-- name    : DataDrivenRO.Moment.theorem_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:24:35.770997+00:00
-- url     : https://prove2.me/theorems/a824dbc0-c60c-44db-b499-b268c2323e4c
-- title:
--   Theorem 10, p. 25 — moment-set support formula and value at risk guarantee
-- statement:
--   Fix $R\ge0$, nonnegative moment thresholds $\Gamma_1,\Gamma_2$, estimates $\hat\mu,\hat\Sigma$, a factor $C$ with $C^\top C=\hat\Sigma+\Gamma_2I$, and $0<\varepsilon<1$. For the moment uncertainty set $\mathcal U^{CS}_{\varepsilon}$ of (35), every $v\in\mathbb R^d$ satisfies
--
--   $$
--   \delta^*(v\mid\mathcal U^{CS}_{\varepsilon})
--   =\hat\mu^\top v+\Gamma_1\|v\|_2+
--   \sqrt{\frac{1-\varepsilon}{\varepsilon}}
--   \sqrt{v^\top(\hat\Sigma+\Gamma_2I)v}.
--   $$
--
--   For every $P\in\mathcal P^{CS}$, its $\operatorname{VaR}^P_{\varepsilon}(v)$ is at most this value. The set $\mathcal U^{CS}_{\varepsilon}$ is nonempty, convex and compact. Thus its support function meets the deterministic criterion of Theorem 1 for every law in the moment region.
--
--   **Formalization Note** This is the deterministic content of Theorem 10 after the sampling data and thresholds are fixed. The paper's statement that the whole family works with sampling probability at least $1-\alpha$ depends on coverage of the confidence region. The bootstrap coverage described on p. 25 is approximate and is not asserted here. Equation (34)'s printed worst-case equality is used only in its upper-bound direction because the confidence region also imposes ball support. `Fin d` is zero-based, and the Lean function type uses an explicit Euclidean norm rather than its default sup norm.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 10 and (34)–(35), p. 25; proof EC.1.7, p. ec8

import Mathlib
import Definitions.Def_DataDrivenRO_Moment_Setting

namespace DataDrivenRO.Moment

/-- The deterministic content of Theorem 10, p. 25: the support formula,
the (34) upper bound for every distribution in the moment region, and the
geometry required to obtain the probabilistic guarantee by Theorem 1. -/
theorem theorem_10 {d : ℕ} (R Γ₁ Γ₂ : ℝ)
    (μhat : Fin d → ℝ) (Shat C : Matrix (Fin d) (Fin d) ℝ)
    (hR : 0 ≤ R) (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂)
    (hC : C.transpose * C = Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∀ v : Fin d → ℝ,
      RobustMDP.Shared.supportFunction (UCS μhat C Γ₁ ε) v =
        csValue μhat Shat Γ₁ Γ₂ ε v) ∧
    (∀ P ∈ PCS R Γ₁ Γ₂ μhat Shat, ∀ v : Fin d → ℝ,
      VaR P ε v ≤ csValue μhat Shat Γ₁ Γ₂ ε v) ∧
    (UCS μhat C Γ₁ ε).Nonempty ∧
    Convex ℝ (UCS μhat C Γ₁ ε) ∧
    IsCompact (UCS μhat C Γ₁ ε) := by sorry

end DataDrivenRO.Moment
