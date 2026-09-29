-- Prove2me | Theorems.Thm_AlonMilman_PropertyT_lemma_4_7
-- name    : AlonMilman.PropertyT.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:32:51.16898+00:00
-- url     : https://prove2.me/theorems/5c0af012-0898-4f08-8359-a4a1c0f9db6b
-- title:
--   Lemma 4.7 — every generating set of a property (T) group is a Kazhdan set
-- statement:
--   Let $H$ be a discrete group having property (T) (Definition 4.6), and let $S \subseteq H$ be a set of generators of $H$ (not necessarily finite). Then there is a constant $\varepsilon > 0$ with the following property: for every essentially nontrivial unitary representation $\pi$ of $H$ in a complex Hilbert space $V$ and every unit vector $y \in V$ there exists $s \in S$ with
--
--   $$\big|\big(\pi(s)y, y\big)\big| < 1 - \varepsilon .$$
--
--   Definition 4.6 provides such a constant for one finite set $K$; the lemma transfers it to an arbitrary generating set. Lemma 4.8 applies it to the representation of $H$ on the zero-sum vectors of a finite quotient.
--
--   **Formalization Note** The Hilbert spaces range over Lean's universe `Type`, as in the definition of property (T). The paper gives no proof and refers to Margulis [27, English version, p. 330].
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), pp. 84–85, Lemma 4.7

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_EssentiallyNontrivial
import Definitions.Def_AlonMilman_PropertyT_HasPropertyT

namespace AlonMilman.PropertyT

/-- Lemma 4.7 (Alon–Milman 1985, pp. 84–85): if `H` is a discrete group having property (T)
and `S` is a set of generators of `H`, there is `ε > 0` such that for every essentially
nontrivial unitary representation `π` of `H` in a complex Hilbert space `V` and every unit
vector `y ∈ V` some `s ∈ S` has `|(π(s) y, y)| < 1 − ε`. -/
theorem lemma_4_7 {H : Type} [Group H] (hH : HasPropertyT H) (S : Set H)
    (hS : Subgroup.closure S = ⊤) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
        (π : H →* unitary (V →L[ℂ] V)), EssentiallyNontrivial π →
        ∀ y : V, ‖y‖ = 1 → ∃ s ∈ S, ‖inner ℂ ((π s : V →L[ℂ] V) y) y‖ < 1 - ε := by sorry

end AlonMilman.PropertyT
