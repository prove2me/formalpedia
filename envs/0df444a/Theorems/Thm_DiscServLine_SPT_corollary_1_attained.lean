-- Prove2me | Theorems.Thm_DiscServLine_SPT_corollary_1_attained
-- name    : DiscServLine.SPT.corollary_1_attained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:18:26.830298+00:00
-- url     : https://prove2.me/theorems/d6517bbf-4a88-4d64-a27e-ef43e8230f40
-- title:
--   Corollary 1, p. 17 (PDF 17) — λ(t) ∝ 1/t³ on a line with t̲ < t̄ attains Q = ½(ln(1 − Λ₁))²
-- statement:
--   Let $\Lambda_0>0$ and $0<\Lambda_1<1$, and put
--   $$\underline t=\frac{1-(1-\Lambda_1)^2}{2\Lambda_0},\qquad \bar t=\frac{\underline t}{1-\Lambda_1},\qquad \lambda(t)=\frac{\underline t}{t^3}\quad(\underline t\le t\le\bar t).$$
--   Then the service line $[\underline t,\bar t]$ with demand schedule $\lambda$ is admissible, offers variety ($\underline t<\bar t$), has throughput $\Lambda_0$ and load $\Lambda_1$, and its SPT queue length is
--   $$Q=\tfrac12\{\ln(1-\Lambda_1)\}^2 .$$
--
--   This is the attainment half of Corollary 1: together with `corollary_1_lower_bound`, the minimum queue length for given $(\Lambda_0,\Lambda_1)$ is $\tfrac12\{\ln(1-\Lambda_1)\}^2$, independent of $\Lambda_0$, attained by a demand schedule proportional to $1/t^3$ on a non-degenerate line. The closed forms of $\underline t$, $\bar t$ and $\lambda$ are those derived in the paper's proof of the corollary.
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), p. 17 (PDF 17), Corollary 1; p. 42 (PDF 42), its proof (printed as "Corollary 2"), closed forms of t̲, t̄ and λ(t)

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model

namespace DiscServLine.SPT

theorem corollary_1_attained (Λ0 Λ1 : ℝ) (h0 : 0 < Λ0) (h1 : 0 < Λ1) (h1' : Λ1 < 1) :
    Admissible (cor1Design Λ0 Λ1) ∧ (cor1Design Λ0 Λ1).lo < (cor1Design Λ0 Λ1).hi ∧
      (cor1Design Λ0 Λ1).Λk 0 = Λ0 ∧ (cor1Design Λ0 Λ1).Λk 1 = Λ1 ∧
      (cor1Design Λ0 Λ1).Q = (1 / 2 : ℝ) * (Real.log (1 - Λ1)) ^ 2 := by sorry

end DiscServLine.SPT
