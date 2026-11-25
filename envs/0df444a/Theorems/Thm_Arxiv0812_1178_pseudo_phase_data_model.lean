-- Prove2me | Theorems.Thm_Arxiv0812_1178_pseudo_phase_data_model
-- name    : Arxiv0812_1178.pseudo_phase_data_model
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T08:51:17.722621+00:00
-- url     : https://prove2.me/theorems/d6f6d622-e26f-454e-a8d6-4729852194bd
-- title:
--   Sec. 3.B, eqs. (24)-(27): the pseudo visibility phase data model
-- statement:
--   Let $N_t\ge3$, let $x\in\mathbb R^P$ be the object and $H(t)$ the complex Fourier matrix, and let $\phi(x,t)=\arg(H(t)x)$. Let $C^\dagger=C^{\mathsf T}(CC^{\mathsf T})^{-1}$.
--
--   1. Suppose the closure data satisfy the model (20) with wrapping vector $\kappa\in\mathbb Z^{(N_t-1)(N_t-2)/2}$:
--   $$\beta^{data}(t)=C\phi(x,t)+\beta^{noise}(t)+2\pi\kappa.$$
--   Then the pseudo phases $\phi^{data}(t)=C^\dagger\beta^{data}(t)$ satisfy, exactly,
--   $$\phi^{data}(t)=\phi(x,t)+\phi^{ker}(t)+C^\dagger\beta^{noise}(t),\qquad\phi^{ker}(t)=(C^\dagger C-\mathrm{Id})\phi(x,t)+2\pi C^\dagger\kappa,$$
--   and $C\phi^{ker}(t)=2\pi\kappa$, so $\phi^{ker}(t)$ lies in the $2\pi$-wrapped kernel of $C$. Consequently there is $\alpha(t)\in\mathbb R^{N_t-1}$ with
--   $$\phi^{data}(t)\equiv\phi(x,t)+\bar B\alpha(t)+C^\dagger\beta^{noise}(t)\pmod{2\pi}\qquad\text{(eq. (27))}.$$
--   2. If $\beta^{noise}(t)\sim\mathcal N(0,R_{\beta(t)})$, then $C^\dagger\beta^{noise}(t)$ has mean $0$ and covariance $R^0_{\phi(t)}=C^\dagger R_{\beta(t)}C^{\dagger\mathsf T}$, and this covariance matrix is singular: $\det R^0_{\phi(t)}=0$.
--
--   This is the pseudo phase data model behind the myopic model of the paper. The unknown aberrations $\alpha(t)$ carry the $N_t-1$ missing phases.
--
--   **Formalization Note** Part 1 holds for every realization of the noise and is stated for an arbitrary noise vector. Part 2 is stated for a random vector whose law is Mathlib's multivariate Gaussian, with a positive semidefinite covariance $R_{\beta(t)}$. The diagonality of $R_{\beta(t)}$ mentioned in Sec. 2.D is not assumed, since the claim does not use it.
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), claim c005; Sec. 3.B, eqs. (23)-(27) and the definition of R^0_phi(t), PDF pp. 8-9

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv0812_1178

theorem pseudo_phase_data_model {n : ℕ} (hn : 3 ≤ n) {P : Type*} [Fintype P]
    (H : Matrix (Baseline n) P ℂ) (x : P → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (βrand : Ω → EuclideanSpace ℝ (ClosureIdx n)) (hβm : Measurable βrand)
    (Rβ : Matrix (ClosureIdx n) (ClosureIdx n) ℝ) (hRβ : Rβ.PosSemidef)
    (hβg : Pr.map βrand = multivariateGaussian 0 Rβ) :
    (∀ (βdata βnoise : ClosureIdx n → ℝ) (κ : ClosureIdx n → ℤ),
      βdata = closureOp n *ᵥ objPhase H x + βnoise + (fun c => 2 * Real.pi * κ c) →
      pseudoPhase n βdata =
          objPhase H x + kerPhase n (objPhase H x) κ + closurePinv n *ᵥ βnoise ∧
        closureOp n *ᵥ kerPhase n (objPhase H x) κ = (fun c => 2 * Real.pi * κ c) ∧
        ∃ (α : Fin (n - 1) → ℝ) (κ' : Baseline n → ℤ),
          pseudoPhase n βdata = objPhase H x + baselineOpBar n *ᵥ α + closurePinv n *ᵥ βnoise +
            (fun b => 2 * Real.pi * κ' b)) ∧
    (∀ b, ∫ ω, (closurePinv n *ᵥ fun c => βrand ω c) b ∂Pr = 0) ∧
    (∀ b b', covariance (fun ω => (closurePinv n *ᵥ fun c => βrand ω c) b)
        (fun ω => (closurePinv n *ᵥ fun c => βrand ω c) b') Pr =
      (closurePinv n * Rβ * (closurePinv n)ᵀ) b b') ∧
    (closurePinv n * Rβ * (closurePinv n)ᵀ).det = 0 := by sorry

end Arxiv0812_1178
