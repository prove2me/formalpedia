-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_theoretical_iInter_mem
-- name    : AssumptionsOfPhysics.theoretical_iInter_mem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T10:04:43.360987+00:00
-- url     : https://prove2.me/theorems/a13ca25e-4349-448b-a682-129aceb1225a
-- title:
--   Theoretical domains are closed under countable conjunction
-- statement:
--   For every experimental domain $\mathcal D$ and every sequence $(s_n)_{n\in\mathbb N}$ of theoretical statements $s_n\in\bar{\mathcal D}$, the countable conjunction $\bigwedge_{n} s_n = \bigcap_n s_n$ is again a theoretical statement.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Proposition 1.37, p. 126

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem theoretical_iInter_mem {Ω : Type*} (D : ExperimentalDomain Ω) (f : ℕ → Set Ω)
    (hf : ∀ n, f n ∈ D.theoretical) : (⋂ n, f n) ∈ D.theoretical := by sorry
end AssumptionsOfPhysics
