-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_exists_pos_forall_integral_eq_mul_setIntegral_iwasawaChart
-- name    : AutomorphicForm.GL2Twisted.exists_pos_forall_integral_eq_mul_setIntegral_iwasawaChart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/a2033a32-3991-5fd0-838a-415fee9420ca
-- title:
--   Iwasawa coordinate integration formula on GL₂(ℂ)
-- statement:
--   Let $\mu$ be a measure on $\mathrm{GL}_2(\mathbb{C})$ for the Borel $\sigma$-algebra `glBorelOf ℂ` attached to the topology of $\mathrm{GL}_2(\mathbb{C})$, and assume $\mu$ is a Haar measure for that $\sigma$-algebra. Then there is a real constant $c>0$, independent of the function below, such that for every $F\colon \mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$ that is Borel measurable and $\mu$-integrable the following hold. Write a point of $(\mathbb{C}\times\mathbb{C})\times(\mathbb{C}\times\mathbb{C})$ as $q$ with real coordinates $\psi=\operatorname{Re}q_{11}$, $\eta=\operatorname{Im}q_{11}$, $\xi_1=\operatorname{Re}q_{12}$, $\xi_2=\operatorname{Im}q_{12}$, $b_1=\operatorname{Re}q_{21}$, $b_2=\operatorname{Im}q_{21}$, and with $z=q_{22}\in\mathbb{C}$; let $W$ be the set where $0<\psi<\pi$, $0<\eta<\pi/2$, $0<\xi_1<2\pi$, $0<\xi_2<2\pi$, $b_1>0$, $b_2>0$ and $z$ arbitrary. Define $\Phi(q)$ to be $1$ unless $b_1>0$ and $b_2>0$, in which case $\Phi(q)$ is the product of `twistedSplitElt` at $(b_1^2,b_2^2,b_1z)$, i.e. the invertible matrix $\begin{pmatrix}\sqrt{b_1^2}&b_1z\\0&\sqrt{b_2^2}\end{pmatrix}$, with `unitaryElt` at $(\psi,\eta,\xi_1,\xi_2)$, i.e. $e^{i\psi}\begin{pmatrix}\cos\eta\,e^{i\xi_1}&\sin\eta\,e^{i\xi_2}\\-\sin\eta\,e^{-i\xi_2}&\cos\eta\,e^{-i\xi_1}\end{pmatrix}$. Then $q\mapsto \bigl(2\sin\eta\cos\eta/(b_1b_2)\bigr)F(\Phi(q))$ is integrable on $W$ for Lebesgue measure on the eight real coordinates, and $\int F\,d\mu$ equals $c$ times the integral of that function over $W$.
--
--   This is the Iwasawa-type integration formula $dg=c\,(db_1\,db_2/b_1b_2)\,d^2z\,dk$ for Haar measure on $\mathrm{GL}_2(\mathbb{C})=ANK$, written in explicit coordinates: upper triangular part with positive real diagonal $(b_1,b_2)$ and shear $z$, times a unitary factor in Hopf coordinates $(\psi,\eta,\xi_1,\xi_2)$ with Haar density $\sin\eta\cos\eta$, the range $0<\psi<\pi$ giving an essentially injective chart. It is obtained from the description of Haar measure on $\mathrm{GL}_2(\mathbb{C})$ by $|\det|^{-4}$ times Lebesgue measure on matrix space together with the Jacobian computation [`AutomorphicForm.GL2Twisted.map_splitProductChart`](thm.html#AutomorphicForm.GL2Twisted.map_splitProductChart), and is used for the evaluation of twisted orbital integrals over the diagonal at a complex place in [`AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage`](thm.html#AutomorphicForm.exists_pos_forall_isOrbitalIntegralOn_diagonal_complex_eq_mul_integral_unitaryAverage).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_exists_pos_forall_integral_eq_mul_setIntegral_iwasawaChart.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.exists_pos_forall_integral_eq_mul_setIntegral_iwasawaChart
    (μ : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : GL (Fin 2) ℂ → ℂ, Measurable[glBorelOf ℂ] F → Integrable F μ →
      IntegrableOn (fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
          ((2 * Real.sin q.1.1.im * Real.cos q.1.1.im / (q.2.1.re * q.2.1.im) : ℝ) : ℂ) *
            F (if h : 0 < q.2.1.re ∧ 0 < q.2.1.im then
                twistedSplitElt (q.2.1.re ^ 2) (q.2.1.im ^ 2) (q.2.1.re * q.2.2) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
                  unitaryElt q.1.1.re q.1.1.im q.1.2.re q.1.2.im
              else 1))
        (({α : ℂ | 0 < α.re ∧ α.re < Real.pi ∧ 0 < α.im ∧ α.im < Real.pi / 2} ×ˢ
            {α : ℂ | 0 < α.re ∧ α.re < 2 * Real.pi ∧ 0 < α.im ∧ α.im < 2 * Real.pi}) ×ˢ
          ({β : ℂ | 0 < β.re ∧ 0 < β.im} ×ˢ (Set.univ : Set ℂ))) volume ∧
      ∫ g, F g ∂μ = (c : ℂ) *
        ∫ q in (({α : ℂ | 0 < α.re ∧ α.re < Real.pi ∧ 0 < α.im ∧ α.im < Real.pi / 2} ×ˢ
            {α : ℂ | 0 < α.re ∧ α.re < 2 * Real.pi ∧ 0 < α.im ∧ α.im < 2 * Real.pi}) ×ˢ
          ({β : ℂ | 0 < β.re ∧ 0 < β.im} ×ˢ (Set.univ : Set ℂ))),
          ((2 * Real.sin q.1.1.im * Real.cos q.1.1.im / (q.2.1.re * q.2.1.im) : ℝ) : ℂ) *
            F (if h : 0 < q.2.1.re ∧ 0 < q.2.1.im then
                twistedSplitElt (q.2.1.re ^ 2) (q.2.1.im ^ 2) (q.2.1.re * q.2.2) ⟨pow_pos h.1 2, pow_pos h.2 2⟩ *
                  unitaryElt q.1.1.re q.1.1.im q.1.2.re q.1.2.im
              else 1) := by sorry
