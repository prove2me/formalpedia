-- Prove2me | Theorems.Thm_CopylessCRA_c2_invertible
-- name    : CopylessCRA.c2_invertible
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:33.891485+00:00
-- url     : https://prove2.me/theorems/49d94710-9649-4925-bd7b-4f6344b48401
-- title:
--   Theorem 1, final claim, p.2 — every function computed by a (C2) machine is invertible
-- statement:
--   Let $f:\Sigma^*\to\mathbb Q$ be computed by a CCRA as in (C2): permutation control, isolated affine register updates $x\mapsto\alpha x+\beta$ with $\alpha\ne0$, outputs linear combinations of products of distinct registers. Then $f$ is an invertible rational series: its minimal letter matrices are invertible.
--
--   Differences from the source:
--   - encoding: $f$ is invertible: its minimal letter matrices are invertible → $f$ has some minimal representation with invertible letter matrices; reason: minimal representations exist for rational series and are unique up to conjugation
--   - encoding: copyless polynomial expressions; (C2)'s isolated updates and output shape → syntax trees with an occurrence multiset (copyless = no repeated occurrence across the tuple); (C2)'s update and output conditions stated on the functions the expressions compute; reason: copylessness is a property of the written expression; a function of the form $\alpha x_i+\beta$ is computed by the literal expression
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Theorem 1 ("Moreover"), p.2 (PDF p.4); proof p.12 (PDF p.14)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsRep

namespace CopylessCRA

/-- **The final claim of Theorem 1.** Every function computed by a machine as in (C2) is invertible:
its minimal letter matrices are invertible.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Theorem 1 ("Moreover"), p.2 (PDF p.4); proof p.12 (PDF p.14).

**Formalization Note** "Invertible" is `IsInvertibleSeries`: `f` has a minimal representation with
invertible letter matrices (in particular `f` is a rational series). -/
theorem c2_invertible {α : Type*} [Fintype α] (f : List α → ℚ) :
    C2 f → IsInvertibleSeries f := by sorry

end CopylessCRA
