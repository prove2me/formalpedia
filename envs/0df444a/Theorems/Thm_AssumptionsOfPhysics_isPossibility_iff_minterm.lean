-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_isPossibility_iff_minterm
-- name    : AssumptionsOfPhysics.isPossibility_iff_minterm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T11:51:30.890004+00:00
-- url     : https://prove2.me/theorems/9ef816a9-b622-4f3d-b9b4-ca8f9a1f2732
-- title:
--   Possibilities are the non-impossible minterms of a basis
-- statement:
--   Let $B$ be a basis of the experimental domain $\mathcal D$. A statement $x$ is a possibility for $\mathcal D$ if and only if $x$ is not impossible and $x$ is a minterm of $B$, i.e. $x=\bigwedge_{b\in B}\ell_b$ where each $\ell_b$ is either $b$ or $\neg b$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Proposition 1.48, p. 130

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem isPossibility_iff_minterm {Ω : Type*} (D : ExperimentalDomain Ω)
    (B : Set (Set Ω)) (hB : IsBasis D.stmts B) (x : Set Ω) :
    D.IsPossibility x ↔ x.Nonempty ∧ ∃ σ : B → Bool, x = minterm B σ := by sorry
end AssumptionsOfPhysics
