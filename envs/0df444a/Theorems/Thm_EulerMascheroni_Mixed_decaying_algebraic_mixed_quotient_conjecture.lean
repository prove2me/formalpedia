-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_decaying_algebraic_mixed_quotient_conjecture
-- name    : EulerMascheroni.Mixed.decaying_algebraic_mixed_quotient_conjecture
-- status  : Open
-- author  : @shivm
-- created : 2026-09-11T14:22:50.695923+00:00
-- url     : https://prove2.me/theorems/b4b0dc92-8ff6-4610-b3ee-43fa4db42b6f
-- title:
--   Conjectural arithmetic quotient for the local mixed E-value relation
-- statement:
--   Let $a,b,c$ be real algebraic numbers such that $\delta=a+b e+c e\operatorname{Ein}(1)$, and let $f_n$ be the Taylor coefficients of that E-function combination. Conjecturally, there is a sequence of algebraic numbers $u_n$ such that
--
--   $$u_0=\delta-f_0,\qquad u_{n+1}=u_n-f_{n+1},\qquad u_n\longrightarrow0.$$
--
--   These are the coefficients of the removable quotient $(\delta-a-be^z-ce^z\operatorname{Ein}(z))/(1-z)$. The convergence follows analytically from the value relation; algebraicity of the coefficients is the unresolved arithmetic assertion. This is an explicit coefficient reformulation of the local intersection gap, not a claim that the gap has become easier or has been proved.
-- source:
--   Fischler–Rivoal, Relations between values of arithmetic Gevrey series, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Conjectures 1–3, Lemma 2(ii), and §4.3. The coefficient formulation here is derived explicitly for this decomposition; it is not claimed to be a newly proved intersection theorem.

import Definitions.Def_eulerMascheroni_mixedCoefficients
open EulerMascheroni.Mixed

theorem EulerMascheroni.Mixed.decaying_algebraic_mixed_quotient_conjecture (a b c : ℝ)
    (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) (hc : IsAlgebraic ℚ c)
    (h : (EulerMascheroni.gompertzConstant:ℂ) =
      (a:ℂ)+(b:ℂ)*Complex.exp 1+(c:ℂ)*EulerMascheroni.Mixed.expEin 1) :
    ∃ u : ℕ → ℂ,
      u 0 = (EulerMascheroni.gompertzConstant:ℂ) -
        EulerMascheroni.Mixed.valueCoefficient a b c 0 ∧
      (∀ n, u (n+1) = u n - EulerMascheroni.Mixed.valueCoefficient a b c (n+1)) ∧
      Filter.Tendsto u Filter.atTop (nhds 0) ∧
      ∀ n, IsAlgebraic ℚ (u n) := by sorry
