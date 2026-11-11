-- Prove2me | Theorems.Thm_CSPIdealMem_lemma_3_4
-- name    : CSPIdealMem.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:29:55.768409+00:00
-- url     : https://prove2.me/theorems/c704b4bf-2128-464a-81a7-1869055b4d79
-- title:
--   Lemma 3.4 — reconstruction from pairs of blocks
-- statement:
--   Let $t:D^p\to D$ be an idempotent cyclic operation of prime arity, and $H\subseteq B_d$ a $\mathbb Q$-subspace closed under $T_t$. A vector $z\in B_d$ belongs to $H$ if and only if
--
--   1. for every block $S$ there is $h\in H$ with $h_S=z_S$, and
--   2. for every pair of distinct blocks $S\neq T$ there is $h\in H$ with $h_S=z_S$ and $h_T=z_T$.
--
--   That is, a closed subspace is determined by its projections onto single blocks and pairs of blocks.
--
--   Differences from the source:
--   - encoding: a nonempty finite domain D ⊆ ℚ (values used only as abstract elements here) → any nonempty finite type α with decidable equality; reason: the statement does not use the rational labels; every finite subset of ℚ is such a type and every such type is in bijection with a finite subset of ℚ, so the two forms are equivalent
--   - encoding: T_t: the blockwise multilinear extension of t, defined on basis vectors by T_{t,S}(e_{a_1}, …, e_{a_k}) = e_{t(a_1, …, a_k)} and extended multilinearly (p.15) → the explicit formula T_t(z)_{S,b} = Σ_{a_1, …, a_k : t(a_1, …, a_k) = b} Π_j (z_j)_{S,a_j}; reason: this is the unique multilinear map with that action on basis vectors (checked on basis vectors in the sanity file)
--   - encoding: "its projection onto each single block and each pair of distinct blocks belongs to the corresponding projection of H" → ∃ h ∈ H agreeing with z on that block (resp. on both blocks); reason: this is the definition of membership in the projection of H
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Lemma 3.4, p.19 (PDF 19)

import Mathlib
import Definitions.Def_CSPIdealMem_Indicator

namespace CSPIdealMem

/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Lemma 3.4 (reconstruction from pairs of blocks), p.19 (PDF 19).

Let `t : α^p → α` be idempotent and cyclic of prime arity `p`, and `H ⊆ B_d` a subspace closed
under `T_t`. A vector `z ∈ B_d` belongs to `H` iff its projection onto each single block and onto
each pair of distinct blocks belongs to the corresponding projection of `H`. -/
theorem lemma_3_4 {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {n d p : ℕ} (hp : p.Prime) (t : (Fin p → α) → α)
    (hti : IsIdempotent t) (htc : IsCyclic t) (H : Submodule ℚ (Bd α n d))
    (hH : ClosedUnder t H) (z : Bd α n d) :
    z ∈ H ↔ (∀ S : Sd n d, ∃ h ∈ H, h S = z S) ∧
      (∀ S T : Sd n d, S ≠ T → ∃ h ∈ H, h S = z S ∧ h T = z T) := by sorry

end CSPIdealMem
