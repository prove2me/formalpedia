-- Prove2me | Theorems.Thm_AgriChain_LandAlloc_theorem_2
-- name    : AgriChain.LandAlloc.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:46:56.952021+00:00
-- url     : https://prove2.me/theorems/d627db8f-0666-45be-aa96-7b61bb541d06
-- title:
--   Theorem 2, p. 14 — the WTPs p̄₁, p̄₂ in closed form (9)–(10)
-- statement:
--   Consider the two-region agri-chain under its standing assumptions ($c_1\le c_2$, $K_1,K_2>0$, $0\le p_o\le p^e-c_2$), and let $y_1=x_1Y^e_1\ge0$, $y_2=x_2Y^e_2\ge0$ be the realized harvests with positive total $T=y_1+y_2>0$. Then the willingness to pay $\bar p_i$ of Processor $i$, defined as the highest admissible price satisfying (7) resp. (8), is attained and equals
--   $$\bar p_1=(p^e-c_1)-\frac{(p^e-c_1-p_o)\min\{K_1,(T-K_2)^+\}}{\min\{K_1,T\}},\qquad \bar p_2=(p^e-c_2)-\frac{(p^e-c_2-p_o)\min\{K_2,(T-K_1)^+\}}{\min\{K_2,T\}} .$$
--
--   The closed forms show that each processor's WTP depends on the harvests only through their total and is independent of the other processor's price; every later result on prices and equilibria uses them.
--
--   **Formalization Note.** The statement asserts that each closed form is the greatest element of the corresponding set of admissible prices (`IsGreatest`), which includes attainment. The hypothesis $T>0$ is the paper's; it makes the denominators positive.
-- source:
--   Li, Kouvelis & Dada, Agricultural Supply Chains in Emerging Markets: Competition and Cooperation under Correlated Yields, SSRN 3531158 (PDF of 2023-01-03), p. 14, Theorem 2, (9)–(10)

import Mathlib
import Definitions.Def_AgriChain_LandAlloc_Model

namespace AgriChain.LandAlloc

theorem theorem_2 (C : Chain) (hC : C.Standing) (y1 y2 : ℝ) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2)
    (hT : 0 < y1 + y2) :
    IsGreatest (wtpSet1 C y1 y2)
        ((C.pe - C.c1) -
          (C.pe - C.c1 - C.po) * min C.K1 (max (y1 + y2 - C.K2) 0) / min C.K1 (y1 + y2)) ∧
      IsGreatest (wtpSet2 C y1 y2)
        ((C.pe - C.c2) -
          (C.pe - C.c2 - C.po) * min C.K2 (max (y1 + y2 - C.K1) 0) / min C.K2 (y1 + y2)) := by sorry

end AgriChain.LandAlloc
