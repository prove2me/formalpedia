-- Prove2me | Theorems.Thm_BudgetCoreExchange_qsat2_sigma2Complete
-- name    : BudgetCoreExchange.qsat2_sigma2Complete
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:24.506606+00:00
-- url     : https://prove2.me/theorems/ff6ab968-9b8c-4f8e-b189-cca4807b5da2
-- title:
--   QSAT$_2$ is $\Sigma_2^p$-complete (cited, Appendix A)
-- statement:
--   The language QSAT$_2$ of DNF formulas $\varphi(x,y)$ for which $\exists x\,\forall y\ \varphi(x,y)$ holds is $\Sigma_2^p$-complete:
--
--   1. QSAT$_2\in\Sigma_2^p$, and
--   2. every $\Sigma_2^p$ language over every finite nonempty alphabet reduces to QSAT$_2$ by a polynomial-time many-one reduction.
--
--   The paper calls QSAT$_2$ "the canonical $\Sigma_2^p$-complete problem" and uses it as the source of its reduction; the fact goes back to Stockmeyer (1976) and Wrathall (1976).
--
--   **Formalization Note** $\Sigma_2^p$ is the $\exists\forall$ class over Cook's Turing machines, and formulas are coded with $n$, $m$ and variable indices in unary.
--
--   Differences from the source:
--   - encoding: Σᵖ₂-hardness (no machine model stated) → every Σᵖ₂ language (∃∀ form, |w|^k certificate bounds, checking language in CookPvsNP.P) over every finite nonempty alphabet ≤ₚ-reduces to the language, in Cook's Turing-machine model; reason: standard definition (Arora–Barak Def. 5.1) on the platform's CookPvsNP framework
--   - encoding: a DNF formula ϕ(x,y) with n + m variables → code over a 7-symbol alphabet with n, m and the variable indices in unary; reason: an input representation polynomially equivalent to the usual one (every variable x₁..xₙ, y₁..yₘ is part of the input)
-- source:
--   Bichler, Waldherr, arXiv:1807.08253v1, Appendix A, p.27 ('the canonical Σᵖ₂-complete problem QSAT₂' and the definition of QSAT₂); cited without proof

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_BudgetCoreExchange_Sigma2P
import Definitions.Def_BudgetCoreExchange_QSAT2

namespace BudgetCoreExchange

/-- **QSAT₂ is Σᵖ₂-complete**, cited in Bichler–Waldherr, arXiv:1807.08253v1, Appendix A, p.27:
"a reduction from the canonical Σᵖ₂-complete problem QSAT₂", with QSAT₂ defined there ("Given a
n + m variable Boolean formula ϕ(x,y) in DNF … is it true that ∃x∀yϕ(x,y)?"). The paper cites the
fact without proof (Stockmeyer 1976, Wrathall 1976).

Both halves are stated: `QSAT2 ∈ Σᵖ₂` and every Σᵖ₂ language over every finite nonempty alphabet
reduces to `QSAT2` in polynomial time.

**Formalization Note.** Σᵖ₂ is the ∃∀ class over Cook's Turing machines (`Sigma2P`), and
formulas are coded with `n`, `m` and the variable indices in unary (`DNF.encode`). -/
theorem qsat2_sigma2Complete : Sigma2Complete QSAT2 := by sorry

end BudgetCoreExchange
