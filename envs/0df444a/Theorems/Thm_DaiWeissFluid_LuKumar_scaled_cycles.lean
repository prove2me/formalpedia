-- Prove2me | Theorems.Thm_DaiWeissFluid_LuKumar_scaled_cycles
-- name    : DaiWeissFluid.LuKumar.scaled_cycles
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:23:05.149979+00:00
-- url     : https://prove2.me/theorems/344d242d-b0a1-4cfe-968f-1354daa5dc1b
-- title:
--   Theorem 5.1 Part I — scaled cycles
-- statement:
--   Under positive service times, (5.1), and $m_2+m_4\ge1$, put $r=m_4/(1-m_2)$ and $s_0=0$, with
--   $$s_n=\sum_{j=0}^{n-1}r^j\frac{m_2+m_4}{1-m_2}.$$
--   There is one Lu–Kumar priority fluid solution starting from $(1,0,0,0)$ such that, for every natural number $n$,
--   $$Q(s_n)=(r^n,0,0,0).$$
--   The same solution realizes every successive cycle, including the periodic boundary case $r=1$.
--
--   **Formalization Note** The sum is empty and equals zero at $n=0$; classes use zero-based Lean indices.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 127, proof of Theorem 5.1, Part I, scaled-cycle display

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace DaiWeissFluid.LuKumar

/-- The one solution realizing all scaled Lu–Kumar cycles, p. 127. -/
theorem scaled_cycles (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k)
    (h51₁ : m 0 + m 3 < 1) (h51₂ : m 1 + m 2 < 1)
    (h52 : 1 ≤ m 1 + m 3) :
    let r : ℝ := m 3 / (1 - m 1)
    let s : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n,
      r ^ j * ((m 1 + m 3) / (1 - m 1))
    ∃ Q T, (luKumar m).IsPrioritySolution piLK Q T ∧
      Q 0 = ![1, 0, 0, 0] ∧
      ∀ n : ℕ, Q (s n) = ![r ^ n, 0, 0, 0] := by sorry

end DaiWeissFluid.LuKumar
