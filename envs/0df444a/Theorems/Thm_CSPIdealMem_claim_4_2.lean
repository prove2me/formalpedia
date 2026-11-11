-- Prove2me | Theorems.Thm_CSPIdealMem_claim_4_2
-- name    : CSPIdealMem.claim_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:30:50.382982+00:00
-- url     : https://prove2.me/theorems/44bb0031-8314-4771-a070-622e1afa3c9f
-- title:
--   Claim 4.2 — $\ker A_P = V_d(\mathrm{Sol}(P))$
-- statement:
--   Assume $\Gamma^*$ has a Taylor polymorphism, let $P$ be an instance and $R=\mathrm{Sol}(P)$. Let $A_P$ be the matrix whose rows are the equations $z_{S,a}=0$ for $a\notin\pi_SR$ and the balance equations of the components with an edge of the graphs $G_{S,T}$, $S\neq T$. Then
--   $$
--   \ker A_P=V_d(R).\tag{4.1}
--   $$
--
--   So the indicator space of the solutions is the kernel of an explicit $\{-1,0,1\}$ matrix computable from projections on at most $2d$ variables.
--
--   Differences from the source:
--   - encoding: a nonempty finite domain D ⊆ ℚ (values used only as abstract elements here) → any nonempty finite type α with decidable equality; reason: the statement does not use the rational labels; every finite subset of ℚ is such a type and every such type is in bijection with a finite subset of ℚ, so the two forms are equivalent
--   - encoding: a finite constraint language Γ (a finite collection of relations R ⊆ D^r) → ConstraintLanguage: relations indexed by a finite type, duplicate names kept (p.10); singleton expansions Γ*, Γ_B add the pins as new indices; reason: Lean convention; duplicate relations change no polymorphism, endomorphism, solution set or complexity
--   - encoding: the matrix A_P and its kernel → the set rowsAP of its rows (linear functionals) and the intersection of their kernels; reason: the same subspace
--   - encoding: edges of G_{S,T} for c ∈ π_{S∪T} R → edges (φ|S, φ|T) for φ ∈ R; reason: the same edge set
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Claim 4.2, (4.1), p.25 (PDF 25); rows of A_P, pp.24–25

import Mathlib
import Definitions.Def_CSPIdealMem_RowsAP

namespace CSPIdealMem

/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Claim 4.2, (4.1), p.25 (PDF 25); the rows of `A_P` are defined on pp.24–25.

Assume `Γ*` has a Taylor polymorphism, let `P` be an instance and `R := Sol(P)`. Then
`ker A_P = V_d(R)`. -/
theorem claim_4_2 {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] (Γ : ConstraintLanguage α)
    (hT : HasTaylorPolymorphism (Γ.withPins Finset.univ)) (P : Instance Γ) (d : ℕ) :
    kerAP d (Sol P) = V d (Sol P) := by sorry

end CSPIdealMem
