-- Prove2me | Theorems.Thm_ApproxIC_UpperBound_delta_sandwich_above
-- name    : ApproxIC.UpperBound.delta_sandwich_above
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:29.380623+00:00
-- url     : https://prove2.me/theorems/03f6a57f-173e-4d50-b756-1487e05e3a9c
-- title:
--   Appendix A, proof of Theorem 1, p. 48 — ∆_L ≤ ∆ ≤ ∆_U a.e. on [p⋆, ν₀]: ∆ is within O(ε^β) of v f(v) − F̄(v)
-- statement:
--   Assume Assumption 1, let $p^\star\in(0,\bar v)$ maximize $R$ on $[0,\bar v]$, let $\beta\in(0,1/2)$, and let $\Delta$ be the dual virtual value of the path of eq. (9) with Lemma 2's dual solution. There are constants $C_L,C_U>0$ and $\varepsilon_0>0$ such that for all $\varepsilon\in(0,\varepsilon_0]$, for almost every $v\in[p^\star,\nu_0]$ (with $\nu_0=\bar v-\varepsilon^\beta$),
--   $$\Delta_L(v):=vf(v)-\bar F(v)-C_L\varepsilon^\beta\ \le\ \Delta(v)\ \le\ vf(v)-\bar F(v)+C_U\varepsilon^\beta=:\Delta_U(v).$$
--
--   Above $p^\star$, the dual virtual value is therefore within $O(\varepsilon^\beta)$ of $-\dot R(v)$; this lets Lemma 4 be applied at $p^\star_L\approx p^\star+\varepsilon^{\beta/(\alpha-1)}$ in the proof of Theorem 1.
--
--   **Formalization Note** This is an unnumbered display in the proof of Theorem 1 (Appendix A, p. 48); the main text (p. 23) states the same sandwich without its range. $C_L,C_U,\varepsilon_0$ are chosen after the distribution, $p^\star$ and $\beta$, and before $\varepsilon$, as "$C_L$ is a positive constant … $\varepsilon>0$ small" on p. 47 says.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), Appendix A, proof of Theorem 1, p. 48, first display (derivation pp. 46–48)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Eq9

namespace ApproxIC.UpperBound

open MeasureTheory

theorem delta_sandwich_above (M : Model) (hM : M.Assumption1) (pstar : ℝ)
    (hp : pstar ∈ Set.Ioo 0 M.vbar) (hmax : IsMaxOn (R M) (Set.Icc 0 M.vbar) pstar)
    (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ CL > 0, ∃ CU > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0,
      ∀ᵐ v ∂(volume.restrict (Set.Icc pstar (nu0Eq9 M.vbar β ε))),
        v * M.f v - cdfBar M v - CL * ε ^ β ≤ DeltaEq9 M pstar β ε v ∧
          DeltaEq9 M pstar β ε v ≤ v * M.f v - cdfBar M v + CU * ε ^ β := by sorry

end ApproxIC.UpperBound
