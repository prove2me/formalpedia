-- Prove2me | Theorems.Thm_Disjunctive_Polarity_facet_characterization_full_row_rank
-- name    : Disjunctive.Polarity.facet_characterization_full_row_rank
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:19:45.158984+00:00
-- url     : https://prove2.me/theorems/36d8fe36-f3e9-4c3c-8774-391462aa041a
-- title:
--   Corollary 2.12 — facets when $B$ has full row rank
-- statement:
--   This is Corollary 2.12 of Balas's *Disjunctive Programming*, cited from [14]: a sharper,
--   transformation-free version of Proposition 2.11 when $B$ has full row rank.
--
--   If $\mathrm{Proj}_x(Q)$ is full-dimensional and $\mathrm{rank}(B) = m$, then $vx \le v_0$ defines
--   a facet of $\mathrm{Proj}_x(Q)$ if and only if $(v,v_0)$ is directly an extreme ray of $\tilde W$
--   — no projection of an auxiliary $w$-coordinate is needed, since full row rank of $B$ makes it
--   unnecessary.
--
--   **Formalization Note.** As in Proposition 2.11, $\tilde W$ (here `Wt`, living directly in
--   $(v,v_0)$-space with no auxiliary coordinate) is taken as given data together with its defining
--   relationship to $\mathrm{Proj}_x(Q)$, per the book's own citation-based treatment.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 32, Corollary 2.12

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

namespace Disjunctive.Polarity

/-- Corollary 2.12 ([14], Balas §2.3, p. 32): when `B` has full row rank, the auxiliary
`w`-coordinate of Proposition 2.11's transformed cone is unnecessary, and `vx ≤ v0` defines a
facet of `Proj_x(Q)` if and only if `(v,v0)` is directly an extreme ray of `W̃` (here `Wt`, taken
via its defining relation `hRepr`, as in Proposition 2.11). -/
theorem facet_characterization_full_row_rank {m p q : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (Wt : Set ((Fin q → ℝ) × ℝ))
    (hFullDim : PolyDim (ProjOntoX (Poly2 A B b)) = (q : ℤ)) (hFullRowRank : B.rank = m)
    (hRepr : ProjOntoX (Poly2 A B b) = {x | ∀ v v0, (v, v0) ∈ Wt → dotProduct v x ≤ v0})
    (v : Fin q → ℝ) (v0 : ℝ) :
    IsFacet (ProjOntoX (Poly2 A B b))
        (ProjOntoX (Poly2 A B b) ∩ {x | dotProduct v x = v0}) ↔
      IsExtremeRay Wt (v, v0) := by sorry

end Disjunctive.Polarity
