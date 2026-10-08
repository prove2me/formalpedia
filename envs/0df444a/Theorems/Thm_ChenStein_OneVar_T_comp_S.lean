-- Prove2me | Theorems.Thm_ChenStein_OneVar_T_comp_S
-- name    : ChenStein.OneVar.T_comp_S
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:30:47.512753+00:00
-- url     : https://prove2.me/theorems/4d635b17-d2fe-4601-b8f2-03053bae7686
-- title:
--   §4, p. 20 — the Poisson Stein inverse identity
-- statement:
--   For every positive Poisson mean $\lambda$ and every function $h:\mathbb N\to\mathbb R$, the Stein operators satisfy
--
--   $$T(Sh)=h.$$
--
--   This identity supplies the inverse equation used to turn a difference in expectations into a Stein-operator expectation. It holds also at $w=0$, where $(Sh)(0)=0$ is fixed by convention.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), §4, p. 20, sentence after definitions of S and T; https://doi.org/10.1214/aop/1176991491

import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting

namespace ChenStein.OneVar

open scoped NNReal

/-- Arratia--Goldstein--Gordon (1989), §4, p. 20: S is inverse to T. -/
theorem T_comp_S (lam : ℝ≥0) (hlam : 0 < lam) (h : ℕ → ℝ) :
    ∀ w : ℕ, T lam (S lam h) w = h w := by sorry

end ChenStein.OneVar
