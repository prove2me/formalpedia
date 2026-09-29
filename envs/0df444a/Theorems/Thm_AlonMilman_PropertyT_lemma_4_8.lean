-- Prove2me | Theorems.Thm_AlonMilman_PropertyT_lemma_4_8
-- name    : AlonMilman.PropertyT.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:34:27.995743+00:00
-- url     : https://prove2.me/theorems/f62246a3-1c02-4fcc-8f38-af5a951aa1da
-- title:
--   Lemma 4.8 — Cayley graphs of finite quotients are (|T|, |S|, ε)-enlargers
-- statement:
--   Let $H$ be a discrete group having property (T), let $S$ be a finite set of generators of $H$ with $S = S^{-1}$, and let $\varepsilon > 0$ be a constant as in Lemma 4.7 for $S$: for every essentially nontrivial unitary representation $\pi$ of $H$ in a complex Hilbert space $V$ and every unit vector $y \in V$ some $s \in S$ has $|(\pi(s)y, y)| < 1 - \varepsilon$. Let $T$ be a finite group with $|T| \ge 2$ and $\phi : H \to T$ a surjective homomorphism. Then the Cayley multigraph $G(T, \phi(S))$, built on the multiset $\phi(S)$ of cardinality $|S|$, is a
--
--   $$(|T|,\ |S|,\ \varepsilon)\text{-enlarger},$$
--
--   that is, it is $|S|$-regular on $|T|$ vertices and $\lambda_1(G(T,\phi(S))) \ge \varepsilon$.
--
--   The lemma turns an analytic property of $H$ into a uniform spectral bound for all Cayley graphs of its finite quotients; Theorem 4.9 follows directly.
--
--   **Formalization Note** The hypothesis $|T| \ge 2$ is added because $\lambda_1$ of a graph on one vertex is undefined (the Lean definition returns $0$ there).
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 85, Lemma 4.8

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_EssentiallyNontrivial
import Definitions.Def_AlonMilman_PropertyT_HasPropertyT
import Definitions.Def_AlonMilman_PropertyT_lambda1
import Definitions.Def_AlonMilman_PropertyT_laplacian
import Definitions.Def_AlonMilman_PropertyT_IsEnlarger
import Definitions.Def_AlonMilman_PropertyT_cayleyMultigraph

namespace AlonMilman.PropertyT

/-- Lemma 4.8 (Alon–Milman 1985, p. 85): let `H` be a discrete group with property (T), `S` a
finite generating set with `S = S⁻¹`, and `ε > 0` a constant as in Lemma 4.7 for `S`.  If
`φ : H →* T` is onto a finite group `T` (with `|T| ≥ 2`), the Cayley multigraph `G(T, φ(S))` is a
`(|T|, |S|, ε)`-enlarger. -/
theorem lemma_4_8 {H : Type} [Group H] (hH : HasPropertyT H) (S : Finset H)
    (hS : Subgroup.closure (S : Set H) = ⊤) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (ε : ℝ) (hε0 : 0 < ε)
    (hε : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
        (π : H →* unitary (V →L[ℂ] V)), EssentiallyNontrivial π →
        ∀ y : V, ‖y‖ = 1 → ∃ s ∈ S, ‖inner ℂ ((π s : V →L[ℂ] V) y) y‖ < 1 - ε)
    {T : Type} [Group T] [Fintype T] [DecidableEq T] (φ : H →* T)
    (hφ : Function.Surjective φ) (hT : 2 ≤ Fintype.card T) :
    IsEnlarger (Fintype.card T) S.card ε (cayleyMultigraph φ S) := by sorry

end AlonMilman.PropertyT
