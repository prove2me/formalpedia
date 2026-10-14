-- Prove2me | Theorems.Thm_CondPortOT_SingDual_proposition_A_5
-- name    : CondPortOT.SingDual.proposition_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:13:16.090036+00:00
-- url     : https://prove2.me/theorems/ea77cd65-8d55-415e-8657-7228df7afcc3
-- title:
--   Proposition A.5, p. 36 — for γ = 0 the worst case equals a sup over υ with Συᵢ = Nε and measures μ₀ⁱ on 𝒴
-- statement:
--   Let $\varepsilon\in(0,1]$ and $\rho>\rho_{\min}(x_0,0,\varepsilon)$, assume Assumption 2.4 with $\gamma=0$ (so the fiber is $\{x_0\}\times\mathcal Y$) and that $x_0$ is not isolated for $\mathbb D_{\mathcal X}$, and let $\ell:\mathcal Y\to\mathbb R$ be measurable. Then
--   $$\sup_{\mathbb Q\in\mathbb B_\rho,\ \mathbb Q(X=x_0)\ge\varepsilon}\mathbb E_{\mathbb Q}[\ell(Y)\mid X=x_0]
--   =\sup_{\substack{\upsilon\in[0,1]^N\\ \sum_i\upsilon_i=N\varepsilon}}\ \sup_{\substack{\mu_0^i\in\mathcal M(\mathcal Y)\ \forall i\\ \sum_i\upsilon_i(\mathbb D_{\mathcal X}(x_0,\hat x_i)+\mathbb E_{\mu_0^i}[\mathbb D_{\mathcal Y}(Y,\hat y_i)])\le N\rho}}(N\varepsilon)^{-1}\sum_{i\in[N]}\upsilon_i\,\mathbb E_{\mu_0^i}[\ell(Y)].$$
--
--   This removes the fractional objective: the mass on the fiber may be fixed at exactly $\varepsilon$, after which the problem is linear in the measures.
--
--   **Formalization Note** $\ell$ stands for $\ell(\cdot,\alpha,\beta)$ at an arbitrary feasible decision. Two hypotheses are added to the page: measurability of $\ell$ (the right side integrates $\ell$ against arbitrary measures), and that $x_0$ is not isolated ($\forall r>0\ \exists x\ne x_0$, $\mathbb D_{\mathcal X}(x,x_0)\le r$). The latter is Assumption 2.4(iii) at $\gamma=0$ with $\partial\{x_0\}$ taken in the ambient space, as the paper's proof uses it to move mass off $\{x_0\}$ at vanishing cost; with the frontier taken in $\mathcal X$ it would be vacuous at an isolated point, where the statement fails. The inner supremum is `innerSup`; the budget is compared in $[0,\infty]$. Expectations of $\ell$ are $\int\ell^+-\int\ell^-$ in $[-\infty,\infty]$. The hypothesis $\rho>\rho_{\min}$ forces $\rho>0$.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 36, Proposition A.5; proof pp. 36–40

import Mathlib
import Definitions.Def_CondPortOT_SingDual_Setting

open MeasureTheory

namespace CondPortOT.SingDual

theorem proposition_A_5 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (hA : Assumption24 DX DY x0 0 xh) (hH1 : CondPortOT.SingUninf.NotIsolated DX x0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ρ : ℝ) (hρ : rhoMin DX DY xh yh x0 0 ε < ENNReal.ofReal ρ)
    (L : Y → ℝ) (hL : Measurable L) :
    worstCaseGe DX DY xh yh x0 0 ρ ε L =
      ⨆ (υ : Fin N → ℝ) (_ : (∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ i, υ i = N * ε),
        innerSup DX DY xh yh x0 ρ ε L υ := by sorry

end CondPortOT.SingDual
