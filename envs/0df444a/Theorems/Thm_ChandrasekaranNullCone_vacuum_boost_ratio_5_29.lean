-- Prove2me | Theorems.Thm_ChandrasekaranNullCone_vacuum_boost_ratio_5_29
-- name    : ChandrasekaranNullCone.vacuum_boost_ratio_5_29
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-26T15:31:24.401399+00:00
-- url     : https://prove2.me/theorems/03e0f758-3302-4c58-8df4-cf975f6d21bd
-- title:
--   Relative boost of the vacuum graviton two-point function, eq. (5.29)
-- statement:
--   Let $c_\perp>0$ and consider the vacuum two-point function of the smeared shear along a null generator,
--   $$G_{\sigma,0}(u,u')=-\frac{c_\perp}{(u-u')^2}\qquad(5.28\text{d}).$$
--   Place the two insertions at $u=-d$ and $u'=d$ with $d>0$, and boost the right insertion by rapidity $\eta\in\mathbb R$. The boost takes $\sigma(u')$ to $e^{\eta}\sigma(e^{\eta}u')$. Then
--   $$\frac{e^{\eta}\,G_{\sigma,0}(-d,e^{\eta}d)}{G_{\sigma,0}(-d,d)}=\frac{4e^{\eta}}{(1+e^{\eta})^{2}},\qquad 1-\frac{4e^{\eta}}{(1+e^{\eta})^{2}}=\tanh^{2}(\eta/2).$$
--
--   **Role in the source.** This is the computation showing that a relative corner boost changes the vacuum correlator across the corner $S$. It reduces the magnitude by the fraction $\tanh^2(\eta/2)$. The boost-invariance contradiction of Appendix D.2 ((D.21)) and the choice of observable in (5.33) rest on it.
--
--   **Formalization note.** The statement is about explicit real functions. $G_{\sigma,0}$ is introduced with `let`, and $c_\perp>0$, $d>0$ are hypotheses as in the source. The source states the fraction in words: the boost "reduces the magnitude of the two point function by a fraction $\tanh^2(\eta/2)+O((\Delta u/d)^2)$" for smeared insertions. The $O((\Delta u/d)^2)$ term is the smearing correction. The second conjunct is the exact identity for point insertions, which is the leading term of that statement.
-- source:
--   Chandrasekaran 2026, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924v1, §5.2, p. 41, eq. (5.29) with the vacuum two-point function eq. (5.28d) and the sentence after Figure 27 ("reduces the magnitude ... by a fraction tanh^2(eta/2)").

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ChandrasekaranNullCone

/-- Chandrasekaran (arXiv:2611.34924), eq. (5.29) with (5.28d): boosting the right insertion of
the vacuum two-point function `G₀(u,u') = -c/(u-u')²` by rapidity `η` multiplies it by
`4e^η/(1+e^η)²`, i.e. reduces its magnitude by the fraction `tanh²(η/2)`. -/
theorem vacuum_boost_ratio_5_29 (c d η : ℝ) (hc : 0 < c) (hd : 0 < d) :
    let G₀ : ℝ → ℝ → ℝ := fun u u' => -c / (u - u') ^ 2
    Real.exp η * G₀ (-d) (Real.exp η * d) / G₀ (-d) d = 4 * Real.exp η / (1 + Real.exp η) ^ 2 ∧
      1 - 4 * Real.exp η / (1 + Real.exp η) ^ 2 = Real.tanh (η / 2) ^ 2 := by sorry

end ChandrasekaranNullCone
