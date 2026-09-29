-- Prove2me | Theorems.Thm_AlonMilman_PropertyT_theorem_4_9
-- name    : AlonMilman.PropertyT.theorem_4_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:34:59.257459+00:00
-- url     : https://prove2.me/theorems/e66ca836-9562-46c4-a0a3-444761a08b35
-- title:
--   Theorem 4.9 — Cayley graphs of finite quotients of a property (T) group form a family of linear enlargers
-- statement:
--   Let $H$ be a discrete group having property (T), and let $S$ be a finite set of generators of $H$ with $S = S^{-1}$. Let $\phi_i : H \to T_i$ ($i = 0, 1, 2, \dots$) be surjective homomorphisms onto finite groups with $|T_i| \to \infty$, and put $G_i = G(T_i, \phi_i(S))$, the Cayley multigraph of $T_i$ with respect to the multiset $\phi_i(S)$. Then $\{G_i\}$ is a family of linear enlargers: there is a fixed $\varepsilon > 0$ such that, with $k = |S|$,
--
--   $$G_i \text{ is a } (|T_i|,\ k,\ \varepsilon)\text{-enlarger for every } i \text{ with } |T_i| \ge 2 .$$
--
--   The constant $\varepsilon$ does not depend on $i$. Combined with Theorem 4.3 of the paper, this gives explicit families of linear expanders and superconcentrators from any property (T) group with infinitely many finite quotients, such as the paper's example $SL(n,\mathbb{Z})$, $n \ge 3$, with its finite quotients.
--
--   **Formalization Note** The guard $|T_i| \ge 2$ excludes the (finitely many, since $|T_i| \to \infty$) trivial quotients, for which $\lambda_1$ is undefined. Graphs are multigraphs with loops, so the degree is exactly $|S|$ even when $\phi_i$ identifies generators or sends one to the identity. The hypothesis $|T_i| \to \infty$ is kept as in the paper.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 85, Theorem 4.9

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_HasPropertyT
import Definitions.Def_AlonMilman_PropertyT_lambda1
import Definitions.Def_AlonMilman_PropertyT_laplacian
import Definitions.Def_AlonMilman_PropertyT_IsEnlarger
import Definitions.Def_AlonMilman_PropertyT_cayleyMultigraph

namespace AlonMilman.PropertyT

/-- Theorem 4.9 (Alon–Milman 1985, p. 85): let `H` be a discrete group with property (T) and
`S` a finite generating set with `S = S⁻¹`.  For surjective homomorphisms `φᵢ : H →* Tᵢ` onto
finite groups with `|Tᵢ| → ∞`, the Cayley multigraphs `Gᵢ = G(Tᵢ, φᵢ(S))` form a family of linear
enlargers: there is one `ε > 0` such that every `Gᵢ` (with `|Tᵢ| ≥ 2`) is a
`(|Tᵢ|, |S|, ε)`-enlarger. -/
theorem theorem_4_9 {H : Type} [Group H] (hH : HasPropertyT H) (S : Finset H)
    (hS : Subgroup.closure (S : Set H) = ⊤) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S)
    (T : ℕ → Type) [∀ i, Group (T i)] [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    (φ : ∀ i, H →* T i) (hφ : ∀ i, Function.Surjective (φ i))
    (hcard : Filter.Tendsto (fun i => Fintype.card (T i)) Filter.atTop Filter.atTop) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 2 ≤ Fintype.card (T i) →
      IsEnlarger (Fintype.card (T i)) S.card ε (cayleyMultigraph (φ i) S) := by sorry

end AlonMilman.PropertyT
