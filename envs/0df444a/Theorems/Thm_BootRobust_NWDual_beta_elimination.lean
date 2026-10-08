-- Prove2me | Theorems.Thm_BootRobust_NWDual_beta_elimination
-- name    : BootRobust.NWDual.beta_elimination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:13:04.019989+00:00
-- url     : https://prove2.me/theorems/7745e60b-81d9-49bb-8b05-318f76ea6644
-- title:
--   B.8, p. 32 — eliminating β: some β satisfies rν + νΣD·exp((a+β)/ν − 1) ≤ β iff ν log ΣD·exp(a/ν) + rν ≤ 0
-- statement:
--   Let $D\in\mathcal D_n$, $a\in\mathbb R^{\Omega_n}$, $\nu>0$ and $r\in\mathbb R$, and write $S=\sum_iD_i\,e^{a_i/\nu}>0$. Consider
--   $$F(\beta)=r\nu+\nu\sum_iD_i\exp\Big(\frac{a_i+\beta}{\nu}-1\Big)-\beta,\qquad\beta\in\mathbb R .$$
--   Then:
--   1. $F$ is minimized at $\beta^\star=\nu-\nu\log S$;
--   2. some $\beta$ satisfies $r\nu+\nu\sum_iD_i\exp\big(\frac{a_i+\beta}{\nu}-1\big)\le\beta$ if and only if
--   $$\nu\log\Big(\sum_i\exp(a_i/\nu)\,D_i\Big)+r\nu\le0 .$$
--
--   With $a_i=(\ell_i-\alpha)w_i$ this turns the dual of the strong-duality step into the dual program (33) of Lemma 2.
--
--   **Formalization Note** The paper prints $\beta^\star=-\nu+\nu\log(\cdot)$; the first-order condition gives $\beta^\star=\nu-\nu\log(\cdot)$, which is what is stated here. The paper's final display (the equivalence in item 2) is unaffected by the slip.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.8 (proof of Lemma 2), p. 32, 'Using first-order optimality conditions, the optimal β⋆ must satisfy …' and the final display

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

namespace BootRobust.NWDual

/-- B.8, p. 32 (elimination of `β`): for `D ∈ Dₙ` and `ν > 0`, the map
`β ↦ r ν + ν ∑ᵢ Dᵢ exp((aᵢ + β)/ν − 1) − β` is minimized at `β⋆ = ν − ν log ∑ᵢ Dᵢ exp(aᵢ/ν)`, and
some `β` satisfies `r ν + ν ∑ᵢ Dᵢ exp((aᵢ + β)/ν − 1) ≤ β` if and only if
`ν log (∑ᵢ exp(aᵢ/ν) Dᵢ) + r ν ≤ 0`. -/
theorem beta_elimination {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (a : ι → ℝ) (ν : ℝ) (hν : 0 < ν) (r : ℝ) :
    (∀ β : ℝ,
      r * ν + ν * ∑ i, D i * Real.exp
          ((a i + (ν - ν * Real.log (∑ j, Real.exp (a j / ν) * D j))) / ν - 1) -
        (ν - ν * Real.log (∑ j, Real.exp (a j / ν) * D j)) ≤
      r * ν + ν * ∑ i, D i * Real.exp ((a i + β) / ν - 1) - β) ∧
    ((∃ β : ℝ, r * ν + ν * ∑ i, D i * Real.exp ((a i + β) / ν - 1) ≤ β) ↔
      ν * Real.log (∑ i, Real.exp (a i / ν) * D i) + r * ν ≤ 0) := by sorry

end BootRobust.NWDual
