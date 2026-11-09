-- Prove2me | Theorems.Thm_CEPolytopeHard_theorem_3_3
-- name    : CEPolytopeHard.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:07.946193+00:00
-- url     : https://prove2.me/theorems/4158c753-4ba2-42f4-8b1b-20628bc3f362
-- title:
--   Theorem 3.3 — $\varepsilon$-fixed sets and $\varepsilon$-convex expected fixed points are equivalent
-- statement:
--   Let $X \subseteq \mathbb R^d$ be convex and compact, $f : X \to X$ continuous, and $\varepsilon \in \mathbb R$.
--
--   1. If $\mu$ is an $\varepsilon$-convex expected fixed point of $f$, then its support $\operatorname{supp}\mu$ is an $\varepsilon$-fixed set of $f$, with a transition matrix on $\operatorname{supp}\mu$ of which $\mu$ is the stationary distribution.
--   2. Conversely, if $S$ is an $\varepsilon$-fixed set of $f$ with transition matrix $P$ and stationary distribution $\mu$, then $\mu$, viewed as a distribution on $X$, is an $\varepsilon$-convex expected fixed point of $f$.
--
--   This duality lets the paper move between the analytic condition produced by correlated equilibria (convex EFPs, Claim 4.4) and the Markov-chain condition used to extract fixed points (fixed sets, Section 3.2).
--
--   Differences from the source:
--   - reading: "the support of an ϵ-convex EFP is also an ϵ-fixed set" → the support is an ε-fixed set with a transition matrix whose stationary distribution is μ itself; reason: the proof constructs P(j | i) = W_ij/µ_i, which has stationary distribution µ; this is the stronger of the two readings
--   - encoding: distributions in ∆(X); S = {x_1, …, x_k} → finitely supported functions (Finsupp); chains indexed by the points of S; reason: Lean representation of finite-support distributions and of a finite set
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 3.3, p.13 (standing assumptions p.13)

import Mathlib
import Definitions.Def_CEPolytopeHard_IsConvexEFP
import Definitions.Def_CEPolytopeHard_IsFixedSet

set_option autoImplicit false

namespace CEPolytopeHard

/-- **Theorem 3.3 (fixed sets and convex expected fixed points are equivalent)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Theorem 3.3,
p.13: "The above two definitions are equivalent. That is, the support of an ϵ-convex EFP is also
an ϵ-fixed set; conversely, given an ϵ-fixed set, the corresponding stationary distribution μ is an
ϵ-convex EFP"; standing assumptions p.13: "Let X ⊂ R^d be convex and compact, and f : X → X be a
continuous function").

Let `X ⊆ ℝ^ι` be convex and compact, `f : X → X` continuous, and `ε ∈ ℝ`.
1. If `μ` is an `ε`-convex EFP of `f`, then its support is an `ε`-fixed set of `f`, witnessed by
   a transition matrix on the support of which `μ` itself is the stationary distribution.
2. If `S` is an `ε`-fixed set of `f` with transition matrix `P` and stationary distribution `μ`,
   then `μ`, as a distribution on `X`, is an `ε`-convex EFP of `f`.

**Formalization Note** In part 1 the stationary distribution is `μ` restricted to its support;
the proof constructs `P(j | i) = W_{ij}/μ_i` with this stationary distribution, which is the
stronger reading of "the support of an ϵ-convex EFP is also an ϵ-fixed set". Norms are normalized
(p.9). -/
theorem theorem_3_3 {ι : Type} [Fintype ι] (X : Set (ι → ℝ)) (hXc : Convex ℝ X)
    (hXk : IsCompact X) (f : (ι → ℝ) → ι → ℝ) (hfX : Set.MapsTo f X X) (hfc : ContinuousOn f X)
    (ε : ℝ) :
    (∀ μ : (ι → ℝ) →₀ ℝ, IsConvexEFP X f ε μ →
      ∃ P : Matrix μ.support μ.support ℝ, IsFixedSetWith X f ε μ.support P (fun x => μ x)) ∧
    (∀ (S : Finset (ι → ℝ)) (P : Matrix S S ℝ) (w : S → ℝ), IsFixedSetWith X f ε S P w →
      IsConvexEFP X f ε (weightsDist S w)) := by sorry

end CEPolytopeHard
