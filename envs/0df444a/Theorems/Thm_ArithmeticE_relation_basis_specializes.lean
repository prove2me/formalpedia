-- Prove2me | Theorems.Thm_ArithmeticE_relation_basis_specializes
-- name    : ArithmeticE.relation_basis_specializes
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T16:37:50.067174+00:00
-- url     : https://prove2.me/theorems/f73c464e-0f9c-4758-bf03-c4421d6a033c
-- title:
--   Beukers relation basis has full rank at every complex specialization
-- statement:
--   Every finite family of complex formal power series admits a polynomial basis for all its polynomial relations whose rows remain linearly independent at every complex point. Explicitly, there exist $r$ polynomial rows $C_j$ such that each $\sum_iC_{ji}f_i=0$, every polynomial relation is a polynomial linear combination of these rows, and $(C_j(\xi))_{j=1}^r$ is linearly independent over $\mathbb C$ for every $\xi\in\mathbb C$. This is the full-rank specialization assertion of Beukers' relation-basis lemma. It follows by evaluating the polynomial left inverse constructed in the proved relation-basis theorem.
-- source:
--   Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Lemma 3.1, pp. 5–6.

import Definitions.Def_beukersLiftingData

theorem ArithmeticE.relation_basis_specializes (m : ℕ) (f : Fin m → PowerSeries ℂ) :
    ∃ (r : ℕ) (C : Fin r → Fin m → Polynomial ℂ),
      (∀ j, ∑ i, (C j i : PowerSeries ℂ) * f i = 0) ∧
      (∀ p : Fin m → Polynomial ℂ, (∑ i, (p i : PowerSeries ℂ) * f i = 0) →
        ∃ b : Fin r → Polynomial ℂ, ∀ i, p i = ∑ j, b j * C j i) ∧
      (∀ ξ : ℂ, LinearIndependent ℂ (fun j i => (C j i).eval ξ)) := by sorry
