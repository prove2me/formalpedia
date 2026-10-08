-- Prove2me | Theorems.Thm_DisplMonoMFG_WellPosed_theorem_6_3
-- name    : DisplMonoMFG.WellPosed.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:44.465355+00:00
-- url     : https://prove2.me/theorems/f38dbd2b-42a0-465e-b9ab-3adc98721bd5
-- title:
--   Theorem 6.3, first sentence — the master equation has a unique global classical solution under displacement monotonicity
-- statement:
--   Let $T>0$ and $\beta\ge0$. Let the terminal cost $G$ satisfy Assumption 3.1, the Hamiltonian $H$ satisfy Assumption 3.2, and let Assumption 3.5 hold: $G$ is displacement monotone (2.16) and $H$ is displacement monotone (3.2). Then the master equation
--   $$
--   \begin{cases}
--   -\partial_tV-\dfrac{1+\beta^2}{2}\operatorname{tr}(\partial_{xx}V)+H(x,\mu,\partial_xV)-\mathcal NV=0 & \text{in }(0,T)\times\mathbb R^d\times\mathcal P_2(\mathbb R^d),\\[4pt]
--   V(T,x,\mu)=G(x,\mu)
--   \end{cases}
--   $$
--   on $[0,T]$ admits a classical solution $V$ with bounded $\partial_xV$, $\partial_{xx}V$, $\partial_\mu V$ and $\partial_{x\mu}V$. It is unique: any other classical solution with these four derivatives bounded coincides with $V$ on $[0,T]\times\mathbb R^d\times\mathcal P_2$.
--
--   This is the main result of the paper. It gives global-in-time well-posedness of second-order master equations with common noise for Hamiltonians that need not be separable in $(\mu,p)$. Displacement monotonicity replaces the Lasry–Lions monotonicity condition.
--
--   **Formalization Note** Only the first sentence of Theorem 6.3 is formalized. The second sentence, on the McKean–Vlasov FBSDEs and the representation formula (6.6), needs stochastic calculus with common noise and is out of scope. The constants $L_0^G,L_1^G,L^H,C_0$ of the assumptions are existentially quantified inside the hypotheses.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), Theorem 6.3 (first sentence), p. 2207

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Master

open MeasureTheory

namespace DisplMonoMFG.WellPosed

/-- Gangbo, Mészáros, Mou, Zhang, Ann. Probab. 50 (2022), Theorem 6.3, first sentence, p. 2207
(PDF p. 30): let Assumptions 3.1, 3.2 and 3.5 hold. Then the master equation (1.1) on `[0, T]`
admits a unique classical solution `V` with bounded `∂_x V`, `∂_xx V`, `∂_μ V` and `∂_xμ V`.
The second sentence (well-posedness of the McKean–Vlasov FBSDEs and the representation (6.6)) is
not formalized. Uniqueness is within the class of classical solutions with these four derivatives
bounded, and equality holds on `Θ = [0, T] × ℝ^d × 𝒫₂`. -/
theorem theorem_6_3 {d : ℕ} (T β : ℝ) (hT : 0 < T) (hβ : 0 ≤ β)
    (H : E d → P2 d → E d → ℝ) (G : E d → P2 d → ℝ)
    (wH : C2W d (E d × E d) ℝ) (wG : C2W d (E d) ℝ)
    (hG : Assm31 G wG) (hH : Assm32 H wH) (hM : Assm35 wG wH) :
    ∃ V : ℝ → E d → P2 d → ℝ, IsClassicalSolBdd β 0 T H G V ∧
      ∀ V' : ℝ → E d → P2 d → ℝ, IsClassicalSolBdd β 0 T H G V' →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : E d) (μ : P2 d), V' t x μ = V t x μ := by sorry

end DisplMonoMFG.WellPosed
