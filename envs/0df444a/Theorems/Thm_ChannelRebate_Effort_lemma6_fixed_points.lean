-- Prove2me | Theorems.Thm_ChannelRebate_Effort_lemma6_fixed_points
-- name    : ChannelRebate.Effort.lemma6_fixed_points
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:26.909311+00:00
-- url     : https://prove2.me/theorems/a74da40d-74fa-4278-b27a-aec4025a9e2b
-- title:
--   Lemma 6, p. 1001 — the fixed points T₁ of m₁ = e̲τ and T₂ of m₂ = ēτ on [0, T₃] exist, are unique, and 0 < T₁ < T₂ < T₃
-- statement:
--   Let $0<c<w<p$, $s<c$, $a>0$, $\xi\sim\mathrm{Uniform}(0,1)$, $V(e)=ae^2/2$. For $T\in[0,T_3]$, $T_3=\frac{(p-c)^3}{2a(p-s)^2}$, consider the contract $(w,u(T),b(T),T)$ with
--   $$u(T)=(w-c)\frac{(p-c)^5}{(p-c)^5-\zeta(T)},\qquad b(T)=s+(w-c)\frac{(p-c)^6-(p-s)\zeta(T)}{(p-c)^6-(p-c)\zeta(T)},\qquad \zeta(T)=4a^2(p-s)^3T^2,$$
--   and let $\underline e$, $\tau$ be evaluated at $u=u(T)$, $b=b(T)$. Put $m_1(T)=\underline e\tau$ and $m_2(T)=\bar e\tau$. Then $m_1$ has exactly one fixed point $T_1\in[0,T_3]$, $m_2$ has exactly one fixed point $T_2\in[0,T_3]$, and
--   $$0<T_1<T_2<T_3.$$
--
--   The interval $(T_1,T_2)$ is where Theorem 2 places the coordinating target.
--
--   **Formalization Note.** The wholesale price $w$ is fixed throughout; $T_1$ and $T_2$ depend on it.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 1001, Lemma 6 (with u(T), b(T), ζ(T), T₃, m₁, m₂ defined just before it); proof p. 1005

import Mathlib
import Definitions.Def_ChannelRebate_Effort_Setting

open MeasureTheory Filter Topology

namespace ChannelRebate.Effort

theorem lemma6_fixed_points
    (p c s w a : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p) (hsc : s < c) (ha : 0 < a) :
    (∃! T₁ : ℝ, IsFixed1 p c s a w T₁) ∧ (∃! T₂ : ℝ, IsFixed2 p c s a w T₂) ∧
      ∀ T₁ T₂ : ℝ, IsFixed1 p c s a w T₁ → IsFixed2 p c s a w T₂ →
        0 < T₁ ∧ T₁ < T₂ ∧ T₂ < T3 p c s a := by sorry

end ChannelRebate.Effort
