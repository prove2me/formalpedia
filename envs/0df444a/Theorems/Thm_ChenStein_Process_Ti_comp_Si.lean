-- Prove2me | Theorems.Thm_ChenStein_Process_Ti_comp_Si
-- name    : ChenStein.Process.Ti_comp_Si
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:32:52.2364+00:00
-- url     : https://prove2.me/theorems/39472346-08d1-456e-8be2-86bc2d13ca01
-- title:
--   §6, p. 22 — the coordinatewise operator S_i inverts T_i: T_iS_ih = h for every h
-- statement:
--   Fix a dimension $d$, a coordinate $i$, and a parameter $\lambda_i>0$. For a function $h:\mathbb Z_+^d\to\mathbb R$ let $S_ih$ be the coordinatewise Stein solution
--   $$(S_ih)(j+e_i)=-\bigl(\lambda_iP(Z_i=j_i)\bigr)^{-1}E\{h(j_1,\dots,Z_i,\dots,j_d)\,1(Z_i\le j_i)\},$$
--   with $Z_i$ Poisson with mean $\lambda_i$ and $(S_ih)(j)=0$ when $j_i=0$, and let $(T_if)(j)=j_if(j)-\lambda_if(j+e_i)$. Then for every $h$ and every $j\in\mathbb Z_+^d$,
--   $$(T_iS_ih)(j)=h(j).$$
--
--   This is the identity "$T(Sh)=h$" of the one-variable Chen–Stein method, applied to the $i$-th coordinate with the other $d-1$ coordinates held fixed. It is what turns $E\,h(W)-E\,(P_ih)(W)$ into an expectation of $T_if_i$ in the proof of Theorem 2.
--
--   **Formalization Note** No boundedness or measurability of $h$ is assumed; the identity is pointwise and involves only finite sums. The value of $S_ih$ at points with $j_i=0$ (fixed to $0$) enters $T_iS_ih$ only multiplied by $j_i=0$.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), p. 22, §6, "As before, for i = 1, ..., d, for all h, T_iS_ih = h"

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_Process_Setting

namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem Ti_comp_Si {d : ℕ} (i : Fin d) (lj : ℝ≥0) (hlj : 0 < lj)
    (h : (Fin d → ℕ) → ℝ) :
    ∀ j, Ti i lj (Si i lj h) j = h j := by sorry

end ChenStein.Process
