-- Prove2me | Theorems.Thm_AvramDividend_BailOut_prop2_overshoot
-- name    : AvramDividend.BailOut.prop2_overshoot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:04:49.751983+00:00
-- url     : https://prove2.me/theorems/73174031-4251-44f4-b9de-2c305e014daf
-- title:
--   Proposition 2, (3.17) — expected discounted undershoot at first passage below $0$
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions, in particular $\psi'(0+)=E[X_1]>-\infty$. Let $q>0$, let $W^{(q)}$, $\overline W^{(q)}$, $\overline Z^{(q)}$ be its scale functions, and let $\Phi(q)$ be the largest root of $\psi=q$. For $x\ge0$ let
--
--   $$T_0^-=\inf\{t\ge0: x+X_t<0\}\qquad(\inf\emptyset=\infty)$$
--
--   be the first passage time of the process started at $x$ below $0$. Then $e^{-qT_0^-}(x+X_{T_0^-})$, set to $0$ on $\{T_0^-=\infty\}$, is integrable and
--
--   $$\mathbf E_x\bigl[e^{-qT_0^-}X_{T_0^-}\bigr]=\overline Z^{(q)}(x)-\psi'(0+)\overline W^{(q)}(x)-DW^{(q)}(x),\qquad D=\frac{q-\psi'(0+)\Phi(q)}{\Phi(q)^2}.$$
--
--   This overshoot identity is an input to the computation of the expected discounted capital injections (4.4) in Theorem 1.
--
--   **Formalization Note** $\mathbf E_x$ and $X$ under $P_x$ are written as $E$ and $x+X$ under $P$. On $\{T_0^-=\infty\}$ the integrand is $0$, which is the paper's convention $e^{-q\infty}=0$. The martingale statements of Proposition 2 and identity (3.16) are not part of this item.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 9, Proposition 2, eq. (3.17)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem prop2_overshoot {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W) (x : ℝ) (hx : 0 ≤ x) :
    let T0 : Ω → ℝ≥0∞ := fun ω => ⨅ (t : ℝ≥0) (_ : x + Lv.X t ω < 0), (t : ℝ≥0∞)
    let f : Ω → ℝ := fun ω =>
      if T0 ω < ⊤ then Real.exp (-q * (T0 ω).toReal) * (x + Lv.X (T0 ω).toNNReal ω) else 0
    let D : ℝ := (q - Lv.psiDerivZero * Lv.triplet.Phi q) / Lv.triplet.Phi q ^ 2
    Integrable f P ∧
      ∫ ω, f ω ∂P = Zbar q W x - Lv.psiDerivZero * Wbar W x - D * W x := by sorry

end AvramDividend.BailOut
