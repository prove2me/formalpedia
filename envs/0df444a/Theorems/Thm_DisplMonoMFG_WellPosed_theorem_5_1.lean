-- Prove2me | Theorems.Thm_DisplMonoMFG_WellPosed_theorem_5_1
-- name    : DisplMonoMFG.WellPosed.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:23.876537+00:00
-- url     : https://prove2.me/theorems/edf775b2-e215-4df9-b523-b5f0c5543f59
-- title:
--   Theorem 5.1 — displacement semimonotone classical solutions are uniformly $W_2$-Lipschitz in $\mu$
-- statement:
--   Let all the conditions of Theorem 4.1 hold except Assumption 3.5(ii). That is:
--   - $G$ satisfies Assumption 3.1 and (2.16);
--   - $H$ satisfies Assumption 3.2(i) and (iv);
--   - $V$ is a classical solution on $[0,T]$ with the further regularity of Theorem 4.1.
--
--   Assume further that, for one $\lambda\ge0$, $V(t,\cdot,\cdot)$ is displacement semimonotone (2.17) for each $t\in[0,T]$. Then there is a constant $C_2^\mu>0$ such that, for all $t\in[0,T]$, $x\in\mathbb R^d$ and $\mu,\nu\in\mathcal P_2$,
--   $$
--   |V(t,x,\mu)-V(t,x,\nu)|\le C_2^\mu\,W_2(\mu,\nu),\qquad|\partial_xV(t,x,\mu)-\partial_xV(t,x,\nu)|\le C_2^\mu\,W_2(\mu,\nu).
--   $$
--   The constant $C_2^\mu$ depends only on $d$, $T$, $\|\partial_xV\|_{L^\infty}$, $\|\partial_{xx}V\|_{L^\infty}$, the constant $L_2^G$ of Remark 3.3(ii), the value $L^H(\|\partial_xV\|_{L^\infty})$ of Assumption 3.2(i), and $\lambda$.
--
--   Combined with Theorem 4.1, this gives the global a priori Lipschitz estimate in the measure variable that the proof of Theorem 6.3 iterates.
--
--   **Formalization Note** "Depends only on" is a quantifier order. $C_2^\mu$ is chosen after $d$, $T$, $\lambda$, $L_2^G$, upper bounds $K_1\ge\|\partial_xV\|_{L^\infty}$ and $K_2\ge\|\partial_{xx}V\|_{L^\infty}$, and a constant $L_h$ for which the bounds of Assumption 3.2(i), and the bound of Assumption 3.2(iv), hold on $D_{K_1}$; this $L_h$ plays the role of $L^H(\|\partial_xV\|_{L^\infty})$. The page has one function $L^H$ for both (i) and (iv), so the value $L^H(\|\partial_xV\|_{L^\infty})$ bounds both. Everything else comes after $C_2^\mu$: $\beta$, $H$, $G$, the function $L^H$, $L_0^G$, $L_1^G$, the further-regularity bounds and $V$. Assumption 3.5(ii) is not assumed.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), Theorem 5.1, p. 2200

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Master

open MeasureTheory

namespace DisplMonoMFG.WellPosed

/-- Gangbo, Mészáros, Mou, Zhang, Ann. Probab. 50 (2022), Theorem 5.1, p. 2200 (PDF p. 23):
under the conditions of Theorem 4.1 without Assumption 3.5(ii), if `V(t,·,·)` satisfies the
displacement semimonotonicity (2.17) (with one `λ`) for each `t ∈ [0, T]`, then `V` and `∂_x V`
are uniformly Lipschitz in `μ` under `W₂` with a constant `C₂^μ > 0` depending only on `d`, `T`,
`‖∂_x V‖_{L^∞}`, `‖∂_xx V‖_{L^∞}`, `L₂^G`, `L^H(‖∂_x V‖_{L^∞})` and `λ`.
Formalization Note: the dependence is the quantifier order — `C` is chosen after `d, T`, upper
bounds `K₁ ≥ ‖∂_x V‖_{L^∞}`, `K₂ ≥ ‖∂_xx V‖_{L^∞}`, `L₂^G`, a constant `Lh` for the bounds of
Assumptions 3.2(i) and 3.2(iv) on `D_{K₁}` (the role of `L^H(‖∂_x V‖_{L^∞})`: the page has one
function `L^H` for both parts), and `λ`, and before everything
else (`β`, `H`, `G`, `L^H`, `L₀^G`, `L₁^G`, the bounds of the further regularity, `V`). -/
theorem theorem_5_1 :
    ∀ (d : ℕ) (T K₁ K₂ L₂ Lh lam : ℝ), 0 < T → 0 ≤ lam → ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 0 ≤ β → ∀ (H : E d → P2 d → E d → ℝ) (G : E d → P2 d → ℝ)
        (wH : C2W d (E d × E d) ℝ) (wG : C2W d (E d) ℝ) (LH : ℝ → ℝ)
        (V Vt : ℝ → E d → P2 d → ℝ) (w : ℝ → C2W d (E d) ℝ),
        Assm31 G wG → Assm32i H wH LH → Assm32iv H wH LH → DisplMono wG →
        LipW2 G wG L₂ → H32iBd wH K₁ Lh → H32ivBd wH K₁ Lh →
        IsClassicalSol β 0 T H G V Vt w → HighReg (Set.Icc 0 T) V w →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : E d) (μ : P2 d),
          ‖(w t).Dx x μ‖ ≤ K₁ ∧ ‖(w t).Dxx x μ‖ ≤ K₂) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, DisplSemimono (w t) lam) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : E d) (μ ν : P2 d),
          |V t x μ - V t x ν| ≤ C * W2 μ ν ∧ ‖(w t).Dx x μ - (w t).Dx x ν‖ ≤ C * W2 μ ν := by sorry

end DisplMonoMFG.WellPosed
