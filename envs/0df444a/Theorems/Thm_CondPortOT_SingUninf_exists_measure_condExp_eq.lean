-- Prove2me | Theorems.Thm_CondPortOT_SingUninf_exists_measure_condExp_eq
-- name    : CondPortOT.SingUninf.exists_measure_condExp_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:19.192729+00:00
-- url     : https://prove2.me/theorems/5567d5cb-7f45-4cc9-80d6-544ac7451418
-- title:
--   pp. 40–41 — for every y₀ there is ℚ′ ∈ 𝔹_ρ with ℚ′(X = x₀) > 0 and E_ℚ′[ℓ(Y) | X = x₀] = ℓ(y₀)
-- statement:
--   Let $\mathcal X$, $\mathcal Y$ be Polish spaces with Borel $\sigma$-algebras, $N\ge1$ samples $(\widehat x_i,\widehat y_i)$, $x_0\in\mathcal X$, and suppose Assumption 2.4 holds with $\gamma=0$ and $x_0$ is not isolated for $\mathbb D_{\mathcal X}$. Let $\rho>0$ and $\ell:\mathcal Y\to\mathbb R$ be any function. Then for every $y_0\in\mathcal Y$ there is $\mathbb Q'\in\mathbb B_\rho$ such that
--
--   $$\mathbb Q'(X=x_0)>0\qquad\text{and}\qquad\mathbb E_{\mathbb Q'}[\ell(Y)\mid X=x_0]=\ell(y_0).$$
--
--   Here $X=x_0$ means $X\in\mathcal N_0(x_0)=\{x:\mathbb D_{\mathcal X}(x,x_0)\le0\}$, which equals $\{x_0\}$ under Assumption 2.4(i). This is the lower-bound half of Proposition 3.1: a small slice of mass moved to $(x_0,y_0)$ makes the conditional law of $Y$ given $X=x_0$ the point mass at $y_0$.
--
--   **Formalization Note** The loss $\ell$ stands for $y\mapsto\ell(y,\alpha,\beta)$ at a fixed decision $(\alpha,\beta)$; no measurability, boundedness or integrability is assumed. The non-isolation hypothesis is an addition to the paper's text: the proof chooses points $x_i'\ne x_0$ at cost at most $\rho/(2N)$ from $\widehat x_i$, which for $\widehat x_i=x_0$ needs points other than $x_0$ arbitrarily close to $x_0$.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, pp. 40–41, proof of Proposition 3.1, construction of ℚ′

import Mathlib
import Definitions.Def_CondPortOT_SingUninf_Setting

open MeasureTheory

namespace CondPortOT.SingUninf

theorem exists_measure_condExp_eq {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (hA : Assumption24 DX DY x0 0 xh) (hH1 : NotIsolated DX x0)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Y → ℝ) (y0 : Y) :
    ∃ Q : Measure (X × Y), InBall DX DY xh yh ρ Q ∧ 0 < Q (fiber DX x0 0) ∧
      condExp Q (fiber DX x0 0) L = (L y0 : EReal) := by sorry

end CondPortOT.SingUninf
