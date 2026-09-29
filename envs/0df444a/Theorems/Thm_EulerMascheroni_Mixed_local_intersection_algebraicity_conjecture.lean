-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_local_intersection_algebraicity_conjecture
-- name    : EulerMascheroni.Mixed.local_intersection_algebraicity_conjecture
-- status  : Open
-- author  : @shivm
-- created : 2026-09-11T13:19:06.206764+00:00
-- url     : https://prove2.me/theorems/2c36eb0c-e7bd-4e6c-b106-6337afa45dc6
-- title:
--   Conjectural E/Y intersection algebraicity for the Gompertz value
-- statement:
--   **Conjectural; no unconditional proof is asserted.** Let $\delta=\int_0^\infty e^{-t}/(1+t)\,dt$ and $A(z)=e^z\operatorname{Ein}(z)$. For real algebraic $a,b,c$, the proposed implication is
--
--   $$\delta=a+be+cA(1)\quad\Longrightarrow\quad\delta\in\overline{\mathbb Q}.$$
--
--   This restricted E/Y intersection statement is a consequence of the conjecture that the common values of E-functions and Borel-summed arithmetic Gevrey series are algebraic. It separates arithmetic compatibility of the two types of values from the known independence of the E-function values.
-- source:
--   Fischler–Rivoal, Relations between values of arithmetic Gevrey series, and applications to values of the Gamma function, JNT 261 (2024), 36–54, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Conjecture 1, p. 2, and §4.3–4.4, pp. 14–15. This is a restricted consequence of Conjecture 1, not an established theorem.

import Definitions.Def_eulerMascheroni_mixedCover

theorem EulerMascheroni.Mixed.local_intersection_algebraicity_conjecture
    (a b c : ℝ) (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b)
    (hc : IsAlgebraic ℚ c)
    (h : (EulerMascheroni.gompertzConstant : ℂ) =
      (a : ℂ) + (b : ℂ) * Complex.exp 1 +
      (c : ℂ) * EulerMascheroni.Mixed.expEin 1) :
    IsAlgebraic ℚ EulerMascheroni.gompertzConstant := by sorry
