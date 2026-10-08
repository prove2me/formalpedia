-- Prove2me | Theorems.Thm_DaiWeissFluid_LuKumar_lyapunov_conditions
-- name    : DaiWeissFluid.LuKumar.lyapunov_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:24:42.257787+00:00
-- url     : https://prove2.me/theorems/25eed6ad-6d29-4a6d-8e74-97e725fa3f74
-- title:
--   Theorem 5.1 Part II — the two Lyapunov conditions
-- statement:
--   Assume positive service times, $m_1+m_4<1$, $m_2+m_3<1$, and $m_2+m_4<1$. Let $Q,T$ be any work-conserving Lu–Kumar fluid solution. Choose $\theta_1,\theta_2$ with $m_1<\theta_1<1-m_4$, $m_2<\theta_2<1-m_3$, and $\theta_2\le\theta_1$. For the functions $G_1,G_2$ of (5.3)–(5.4), both displayed minimum drift constants below are strictly positive. Their derivatives at positive regular times satisfy
--   $$W_1(t)>0\Rightarrow\dot G_1(t)\le-\min\{\theta_1\mu_1-1,(1-\theta_1)\mu_4-1\},$$
--   $$W_2(t)>0\Rightarrow\dot G_2(t)\le-\min\{\theta_2\mu_2-1,(1-\theta_2)\mu_3-1\}.$$
--   At every nonnegative time, $W_2(t)=0$ implies $G_2(t)\le G_1(t)$, and $W_1(t)=0$ implies $G_1(t)\le G_2(t)$. Thus the two components satisfy conditions (a) and (b) of Lemma 3.2.
--
--   **Formalization Note** Regular-point derivatives use `HasDerivAt`; the hypotheses do not require differentiability everywhere. The printed line on p. 127 has $(1-\theta_2)Q_4$ where the intended coefficient is $(1-\theta_1)$, as confirmed by (5.3).
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), pp. 127–128, proof of Theorem 5.1, Part II, (5.3)–(5.4), conditions (a) and (b); corrected coefficient in p. 127 display

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace DaiWeissFluid.LuKumar

/-- The components (5.3)–(5.4) satisfy conditions (a) and (b) of Lemma 3.2. -/
theorem lyapunov_conditions (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : m 1 + m 3 < 1)
    (θ1 θ2 : ℝ)
    (hθ1a : m 0 < θ1) (hθ1b : θ1 < 1 - m 3)
    (hθ2a : m 1 < θ2) (hθ2b : θ2 < 1 - m 2)
    (hθorder : θ2 ≤ θ1)
    (Q T : ℝ → Fin 4 → ℝ) (hsol : (luKumar m).IsWorkConserving Q T) :
    (0 < min (θ1 * (m 0)⁻¹ - 1) ((1 - θ1) * (m 3)⁻¹ - 1)) ∧
    (0 < min (θ2 * (m 1)⁻¹ - 1) ((1 - θ2) * (m 2)⁻¹ - 1)) ∧
    (∀ t d, 0 < t → 0 < (luKumar m).volume Q 0 t →
      HasDerivAt (G1 θ1 Q) d t →
      d ≤ -min (θ1 * (m 0)⁻¹ - 1) ((1 - θ1) * (m 3)⁻¹ - 1)) ∧
    (∀ t d, 0 < t → 0 < (luKumar m).volume Q 1 t →
      HasDerivAt (G2 θ2 Q) d t →
      d ≤ -min (θ2 * (m 1)⁻¹ - 1) ((1 - θ2) * (m 2)⁻¹ - 1)) ∧
    (∀ t, 0 ≤ t → (luKumar m).volume Q 1 t = 0 → G2 θ2 Q t ≤ G1 θ1 Q t) ∧
    (∀ t, 0 ≤ t → (luKumar m).volume Q 0 t = 0 → G1 θ1 Q t ≤ G2 θ2 Q t) := by sorry

end DaiWeissFluid.LuKumar
