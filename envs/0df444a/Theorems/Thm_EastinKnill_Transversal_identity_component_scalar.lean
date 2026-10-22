-- Prove2me | Theorems.Thm_EastinKnill_Transversal_identity_component_scalar
-- name    : EastinKnill.Transversal.identity_component_scalar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:52.683292+00:00
-- url     : https://prove2.me/theorems/3c1ac78c-bb02-4b62-953c-72ad19888f9d
-- title:
--   Proof of Theorem 1, p. 3 — the identity component $\mathcal C$ of $\mathcal G$ acts on the code space as a scalar
-- statement:
--   Let $P$ be the projector of a local-error-detecting code on a composite system, and let $\mathcal G$ be the set of logical unitary product operators. Let $\mathcal C$ be the connected component of the identity in $\mathcal G$. Then every $C \in \mathcal C$ acts on the code space as a scalar: there is $c\in\mathbb C$ with
--
--   $$C\,P = c\,P.$$
--
--   This is the heart of the proof of Theorem 1: the continuous part of the transversal logical group does nothing on the encoded system beyond a global phase.
--
--   **Formalization Note** The page concludes that "the constant of proportionality must be one", so that $CP = P$. That is a slip: the global phase $e^{i\theta}I$ is a unitary product operator, is logical, lies in $\mathcal C$, and satisfies $CP = e^{i\theta}P$. The statement therefore asserts $CP \propto P$, which is what the page's argument proves and all that Theorem 1 needs. $\mathcal C$ is `connectedComponentIn` of $\mathcal G$ at the identity, in the subspace topology of the unitary group.
-- source:
--   Eastin & Knill, Restrictions on Transversal Encoded Quantum Gate Sets, arXiv:0811.4262v2, p. 3, proof of Theorem 1, display "CP = Π_k e^{iD_k}P ∝ P" and the following sentences

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix

namespace EastinKnill.Transversal

theorem identity_component_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    [∀ j, DecidableEq (α j)]
    (P : Matrix (∀ j, α j) (∀ j, α j) ℂ) (hP : IsCodeProjector P)
    (hdet : IsLocalErrorDetecting P) :
    ∀ C ∈ connectedComponentIn (logicalProductUnitaries α P) 1,
      ∃ c : ℂ, (C : Matrix (∀ j, α j) (∀ j, α j) ℂ) * P = c • P := by sorry

end EastinKnill.Transversal
