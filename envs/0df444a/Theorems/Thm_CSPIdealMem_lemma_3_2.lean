-- Prove2me | Theorems.Thm_CSPIdealMem_lemma_3_2
-- name    : CSPIdealMem.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:29:52.919356+00:00
-- url     : https://prove2.me/theorems/b6560761-d015-4218-8499-8af6c4775ccf
-- title:
--   Lemma 3.2 — products, and integral diagonal products, span a $T_t$-closed subspace
-- statement:
--   Let $p$ be prime, $t:D^p\to D$ an idempotent cyclic operation, and $H\subseteq B_d$ a $\mathbb Q$-subspace closed under $T_t$. Then
--   $$
--   H=\mathrm{span}_{\mathbb Q}\{T_t(h_1,\dots,h_p): h_1,\dots,h_p\in H\},
--   $$
--   and in fact the diagonal products $T_t(v,\dots,v)$ with $v\in H\cap\mathbb Z^N$ span $H$.
--
--   This spanning property drives the distributive law for absorbing subspaces.
--
--   Differences from the source:
--   - encoding: a nonempty finite domain D ⊆ ℚ (values used only as abstract elements here) → any nonempty finite type α with decidable equality; reason: the statement does not use the rational labels; every finite subset of ℚ is such a type and every such type is in bijection with a finite subset of ℚ, so the two forms are equivalent
--   - encoding: T_t: the blockwise multilinear extension of t, defined on basis vectors by T_{t,S}(e_{a_1}, …, e_{a_k}) = e_{t(a_1, …, a_k)} and extended multilinearly (p.15) → the explicit formula T_t(z)_{S,b} = Σ_{a_1, …, a_k : t(a_1, …, a_k) = b} Π_j (z_j)_{S,a_j}; reason: this is the unique multilinear map with that action on basis vectors (checked on basis vectors in the sanity file)
--   - encoding: v ∈ H ∩ Z^N (integral vectors of H in the fixed coordinates of B_d ≅ Q^N) → v ∈ H with every coordinate z_{S,a} an integer (IsIntegral); reason: the same set: the coordinates of B_d are the z_{S,a}
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Lemma 3.2, p.17 (PDF 17)

import Mathlib
import Definitions.Def_CSPIdealMem_Indicator

namespace CSPIdealMem

/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Lemma 3.2, p.17 (PDF 17).

Let `p` be prime and `t : α^p → α` idempotent and cyclic. If the subspace `H ⊆ B_d` is closed under
`T_t`, then `H = span_ℚ {T_t(h_1, …, h_p) : h_1, …, h_p ∈ H}`; in fact the diagonal products
`T_t(v, …, v)` with `v ∈ H ∩ ℤ^N` span `H`. -/
theorem lemma_3_2 {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {n d p : ℕ} (hp : p.Prime) (t : (Fin p → α) → α)
    (hti : IsIdempotent t) (htc : IsCyclic t) (H : Submodule ℚ (Bd α n d))
    (hH : ClosedUnder t H) :
    H = Submodule.span ℚ {w | ∃ h : Fin p → Bd α n d, (∀ j, h j ∈ H) ∧ w = Tt t h} ∧
    H = Submodule.span ℚ {w | ∃ v ∈ H, IsIntegral v ∧ w = Tt t (fun _ => v)} := by sorry

end CSPIdealMem
