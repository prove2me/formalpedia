-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_potential_determines_law
-- name    : CasinoCPT.Embedding.potential_determines_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:37.755376+00:00
-- url     : https://prove2.me/theorems/545fdb08-aa96-496e-afaa-245a6c07a510
-- title:
--   §3, p. 13 — the potential determines the law (on ℝ, and at the integers)
-- statement:
--   Let $\mu,\nu\in\mathcal P_0(\mathbb Z)$. Then
--   $$U_\mu=U_\nu\text{ on }\mathbb R\iff\mu=\nu,\qquad\text{and}\qquad U_\mu(x)=U_\nu(x)\ \ \forall x\in\mathbb Z\iff\mu=\nu.$$
--
--   Two centred laws are identical exactly when their potential functions are identical. The integer form is the one used in the proof of Proposition A.3 (p. 46), where $S_\tau\sim\mu$ is shown by checking $U_{S_\tau}(x)=U_\mu(x)$ for all $x\in\mathbb Z$.
--
--   **Formalization Note.** The paper states this for centred laws on $\mathbb R$ with finite first moment (citing Obłój 2004); here both laws live on $\mathbb Z$, which is the case the paper uses.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 13, §3 (used in the proof of Proposition A.3, p. 46)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- §3, p. 13 (and its use in the proof of Proposition A.3, p. 46): two laws in `𝒫₀(ℤ)` are
equal if and only if their potentials agree on `ℝ`, and if and only if their potentials agree
on `ℤ`. -/
theorem potential_determines_law (μ ν : Measure ℤ) (hμ : InP0Z μ) (hν : InP0Z ν) :
    ((∀ x : ℝ, potential μ x = potential ν x) ↔ μ = ν) ∧
      ((∀ x : ℤ, potential μ (x : ℝ) = potential ν (x : ℝ)) ↔ μ = ν) := by sorry

end CasinoCPT.Embedding
