-- Prove2me | Theorems.Thm_DirectedOpinion_Memory_coefficient_bound
-- name    : DirectedOpinion.Memory.coefficient_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:07.617182+00:00
-- url     : https://prove2.me/theorems/1bbc9227-e284-46aa-a041-a75eeb4c658b
-- title:
--   Proof of Proposition 6 — p_m ∈ (0,1), E[(c+d)^{−2(T+2)}] = (1−ρ₂)/((c+d)²((c+d)²−ρ₂)), and the coefficient of E[Var(𝓩₁|𝓧₁)] is ≤ 0
-- statement:
--   Let $c,d>0$ with $c+d<1$, and let $0\le\rho_2\le c^2$. For $m\ge0$ let
--   $$p_m=\sum_{s=0}^\infty\binom{s+m}{s}^2(1-c-d)^{2s}(c+d)^{2(m+1)},$$
--   and let $T$ be a Geometric random variable on $\{0,1,2,\dots\}$ with success probability $1-\rho_2$, i.e. $P(T=k)=\rho_2^k(1-\rho_2)$. Then
--
--   1. $p_m\in(0,1)$ for every $m\ge0$;
--   2. $\displaystyle E\big[(c+d)^{-2(T+2)}\big]=\frac{1}{(c+d)^4}\sum_{k=0}^\infty\rho_2^k(1-\rho_2)(c+d)^{-2k}=\frac{1-\rho_2}{(c+d)^2((c+d)^2-\rho_2)}$;
--   3. the coefficient of $E[\mathrm{Var}(\mathcal Z_1\mid\mathcal X_1)]$ in the variance of $\mathcal M^*$ is nonpositive:
--   $$\frac{1}{1-\rho_2}E\big[(c+d)^{-2(T+2)}p_{T+1}\big]-\frac{1}{(c+d)^2((c+d)^2-\rho_2)}\le 0.$$
--
--   Together with the sign of the coefficient $2d^2(c+d-1)/((c+d)^2(2-(c+d)))<0$, this is the inequality that turns Remark 10.2 and (15) into Proposition 6.
--
--   **Formalization Note.** The statement is deterministic: $\rho_2$ is a real parameter. In the application $\rho_2=E[\sum_{i=1}^{\mathcal N_1}\mathcal C_{(1,i)}^2]$, and $\rho_2\le c^2$ holds there because $\sum\mathcal C^2\le(\sum\mathcal C)^2=c^2$ for nonnegative weights summing to $c$; this is the disclosed hypothesis that replaces the model. $E[g(T)]$ is the series $\sum_k\rho_2^k(1-\rho_2)g(k)$ (`geomExp`), and $(c+d)^{-2(T+2)}$ is `((c + d) ^ (2 * (k + 2)))⁻¹`. The page asserts $p_{T+1}\in(0,1)$; item 1 states it for every index, which is true for $c+d<1$ (it fails only at $c+d=1$, where $p_m=1$).
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, pp. 31–32, proof of Proposition 6

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting

namespace DirectedOpinion.Memory
open MeasureTheory ProbabilityTheory

/-- Proof of Proposition 6, pp. 31–32: for 0 < c, 0 < d, c + d < 1 and 0 ≤ ρ₂ ≤ c², every
p_m lies in (0, 1), E[(c+d)^{−2(T+2)}] = (1 − ρ₂)/((c+d)²((c+d)² − ρ₂)) for T Geometric on
{0, 1, …} with success probability 1 − ρ₂, and the coefficient of E[Var(𝓩₁ | 𝓧₁)] in
Var(𝓜*) is nonpositive. -/
theorem coefficient_bound (c d ρ₂ : ℝ) (hc : 0 < c) (hd : 0 < d) (hcd : c + d < 1)
    (hρ₂ : 0 ≤ ρ₂) (hρ₂c : ρ₂ ≤ c ^ 2) :
    (∀ m : ℕ, pT c d m ∈ Set.Ioo (0 : ℝ) 1) ∧
    geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹)
      = (1 - ρ₂) / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)) ∧
    1 / (1 - ρ₂) * geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
      - 1 / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)) ≤ 0 := by sorry

end DirectedOpinion.Memory
