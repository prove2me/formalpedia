-- Prove2me | Theorems.Thm_FlagshipMEA_Monopoly_proposition_1
-- name    : FlagshipMEA.Monopoly.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:58.992217+00:00
-- url     : https://prove2.me/theorems/3c79490a-e983-4f05-90d3-5c1e5fedfff4
-- title:
--   Proposition 1, pinned down — optimal effort concentrates when transformed cost is concave
-- statement:
--   Consider the firm's profit maximization program (8) with positive markups, positive logit taste scale $\lambda$, and a strictly increasing, convex, continuously differentiable cost on feasible utility increases $[\theta,\infty)$. If $f_c(v)=c(\lambda\log v)$ is concave on $[e^{\theta/\lambda},\infty)$, an optimal allocation exists and at least one optimal allocation is either concentrated on a single product or has zero effort. If the products' pairs $(u_i,\pi_i)$ are pairwise distinct, every optimal allocation has one of those two forms:
--
--   $$\exists m^*\in\operatorname*{arg\,max}_{m_i\geq0}P(m),\qquad \exists m^*\text{ optimal with }\bigl(m^*=0\text{ or }m^*\text{ concentrated}\bigr),$$
--   $$\bigl((u_i,\pi_i)\text{ pairwise distinct}\bigr)\Longrightarrow\bigl(\forall m^*\text{ optimal},\ m^*=0\text{ or }m^*\text{ concentrated}\bigr).$$
--
--   The result characterizes when a product line can direct all positive marketing effort to one flagship product. **Formalization Note** Zero effort is separated because Definition 1 excludes it and can be optimal. Pairwise distinct products rule out mixed optima created by identical products. The paper's undefined phrase “generically unique” is not formalized; the claim here is the concentration statement established by the appendix.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), p. 11 (PDF 13), Proposition 1; proof pp. 40–43 (PDF 42–45)

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

namespace FlagshipMEA.Monopoly

/-- Proposition 1 (p. 11), pinned down: an optimum exists; some optimum is
concentrated or zero; with pairwise distinct products every optimum is so. -/
theorem proposition_1 {n : ℕ} (D : Data n) (hS : D.Standing) (hfc : D.FcConcave) :
    (∃ m, D.IsOptimal m) ∧
    (∃ m, D.IsOptimal m ∧ (IsConcentrated m ∨ m = 0)) ∧
    (D.Distinct → ∀ m, D.IsOptimal m → IsConcentrated m ∨ m = 0) := by sorry

end FlagshipMEA.Monopoly
