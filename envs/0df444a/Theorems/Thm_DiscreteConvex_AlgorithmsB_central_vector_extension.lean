-- Prove2me | Theorems.Thm_DiscreteConvex_AlgorithmsB_central_vector_extension
-- name    : DiscreteConvex.AlgorithmsB.central_vector_extension
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T04:12:12.802984+00:00
-- url     : https://prove2.me/theorems/d1d38d0d-886d-4f4b-939b-8b7d3fab8994
-- title:
--   Proposition 10.5 -- central_vector_extension
-- statement:
--   **Proposition 10.5** (p.285). If $x\in B$ and $u
--   otin V^\circ(x)$, some $x'\in B$ has $V^\circ(x')\supseteq V^\circ(x)\cup\{u\}$.
--
--   **Not in this chunk's own `BRIEF.md` table** — found by direct reading, immediately following the domain reduction algorithm's own description and used in the proof of Proposition 10.6. Formalized as the existence claim its own proof establishes (the specific witness $x'$ is constructed by an explicit recursive procedure the book describes, but the proposition's own logical content is the existence of such an $x'$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.285, Proposition 10.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.285, Proposition 10.5

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_AlgorithmsB_VCirc

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 10.5 (p.285). If `x∈B` and `u∉V°(x)`, some `x'∈B` has `V°(x')⊇V°(x)∪{u}`. `B` is
bounded, as the page's base polyhedron is: `LBCirc` and `UBCirc` are an infimum and a supremum
over `B`, so on an unbounded `B` they read junk values and `V°(x')` is empty for every `x'`
(`B = {x : x₁ + x₂ = 0, x₁ ≥ 5}` satisfies the exchange axiom and refutes the statement). -/
theorem central_vector_extension (B : Set (V → ℤ)) (hB : ExchangeAxiomB B) (hBbdd : B.Finite)
    (x : V → ℤ)
    (hx : x ∈ B) (u : V) (hu : u ∉ VCirc B x) :
    ∃ x' : V → ℤ, x' ∈ B ∧ VCirc B x ⊆ VCirc B x' ∧ u ∈ VCirc B x' := by sorry

end DiscreteConvex.AlgorithmsB
