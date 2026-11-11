-- Prove2me | Theorems.Thm_CSPIdealMem_lemma_3_3
-- name    : CSPIdealMem.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:29:53.414751+00:00
-- url     : https://prove2.me/theorems/8038ddb9-9398-46d5-a934-124f1f43141b
-- title:
--   Lemma 3.3 — distributivity of absorbing subspaces
-- statement:
--   Let $t:D^p\to D$ be an idempotent cyclic operation of prime arity, and $H\subseteq B_d$ a $\mathbb Q$-subspace closed under $T_t$. If $J,K,L\subseteq H$ are subspaces, each absorbing for $T_t$, then
--   $$
--   J\cap(K+L)=(J\cap K)+(J\cap L),\qquad (J+L)\cap(K+L)=(J\cap K)+L.
--   $$
--
--   The second identity is the gluing step of the reconstruction from pairs of blocks.
--
--   Differences from the source:
--   - encoding: a nonempty finite domain D ⊆ ℚ (values used only as abstract elements here) → any nonempty finite type α with decidable equality; reason: the statement does not use the rational labels; every finite subset of ℚ is such a type and every such type is in bijection with a finite subset of ℚ, so the two forms are equivalent
--   - encoding: T_t: the blockwise multilinear extension of t, defined on basis vectors by T_{t,S}(e_{a_1}, …, e_{a_k}) = e_{t(a_1, …, a_k)} and extended multilinearly (p.15) → the explicit formula T_t(z)_{S,b} = Σ_{a_1, …, a_k : t(a_1, …, a_k) = b} Π_j (z_j)_{S,a_j}; reason: this is the unique multilinear map with that action on basis vectors (checked on basis vectors in the sanity file)
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Lemma 3.3, p.19 (PDF 19)

import Mathlib
import Definitions.Def_CSPIdealMem_Indicator

namespace CSPIdealMem

/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Lemma 3.3 (distributivity of absorbing subspaces), p.19 (PDF 19).

Let `t : α^p → α` be idempotent and cyclic of prime arity `p`, and `H ⊆ B_d` a subspace closed
under `T_t`. For subspaces `J, K, L ⊆ H`, each absorbing for `T_t`:
`J ∩ (K + L) = (J ∩ K) + (J ∩ L)` and `(J + L) ∩ (K + L) = (J ∩ K) + L`. -/
theorem lemma_3_3 {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {n d p : ℕ} (hp : p.Prime) (t : (Fin p → α) → α)
    (hti : IsIdempotent t) (htc : IsCyclic t) (H : Submodule ℚ (Bd α n d))
    (hH : ClosedUnder t H) (J K L : Submodule ℚ (Bd α n d))
    (hJ : Absorbing t H J) (hK : Absorbing t H K) (hL : Absorbing t H L) :
    J ⊓ (K ⊔ L) = (J ⊓ K) ⊔ (J ⊓ L) ∧ (J ⊔ L) ⊓ (K ⊔ L) = (J ⊓ K) ⊔ L := by sorry

end CSPIdealMem
