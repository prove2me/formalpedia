-- Prove2me | Theorems.Thm_CSPIdealMem_lemma_3_1
-- name    : CSPIdealMem.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:29:38.415219+00:00
-- url     : https://prove2.me/theorems/2b13f2b6-32c5-4d6e-a68a-aaac78f4a728
-- title:
--   Lemma 3.1 — $T_t$ maps indicator vectors to indicator vectors and preserves $V_d(R)$
-- statement:
--   Let $t:D^k\to D$ be any operation and $T_t$ its blockwise multilinear extension. For all assignments $\varphi_1,\dots,\varphi_k\in D^X$,
--   $$
--   T_t\bigl(\eta_d(\varphi_1),\dots,\eta_d(\varphi_k)\bigr)=\eta_d\bigl(t(\varphi_1,\dots,\varphi_k)\bigr),
--   $$
--   where $t$ acts pointwise on assignments. If $t$ preserves $R\subseteq D^X$, then $V_d(R)$ is closed under $T_t$.
--
--   This turns closure of a relation under a polymorphism into closure of a vector space under a multilinear map.
--
--   Differences from the source:
--   - encoding: a nonempty finite domain D ⊆ ℚ (values used only as abstract elements here) → any nonempty finite type α with decidable equality; reason: the statement does not use the rational labels; every finite subset of ℚ is such a type and every such type is in bijection with a finite subset of ℚ, so the two forms are equivalent
--   - encoding: T_t: the blockwise multilinear extension of t, defined on basis vectors by T_{t,S}(e_{a_1}, …, e_{a_k}) = e_{t(a_1, …, a_k)} and extended multilinearly (p.15) → the explicit formula T_t(z)_{S,b} = Σ_{a_1, …, a_k : t(a_1, …, a_k) = b} Π_j (z_j)_{S,a_j}; reason: this is the unique multilinear map with that action on basis vectors (checked on basis vectors in the sanity file)
--   - generalization: a k-ary operation t : D^k → D with k ≥ 1 (p.3) → any k : ℕ, including k = 0; reason: the k ≥ 1 instances are exactly the source's statement, and at k = 0 both clauses still hold (T_t is the constant indicator of the constant t())
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Lemma 3.1, p.15 (PDF 15)

import Mathlib
import Definitions.Def_CSPIdealMem_Indicator

namespace CSPIdealMem

/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Lemma 3.1, p.15 (PDF 15).

For every operation `t : α^k → α` and all assignments `φ_1, …, φ_k`,
`T_t(η_d(φ_1), …, η_d(φ_k)) = η_d(t(φ_1, …, φ_k))`; and if `t` preserves `R ⊆ α^X` then `V_d(R)` is
closed under `T_t`. -/
theorem lemma_3_1 {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] {n d k : ℕ} (t : (Fin k → α) → α) :
    (∀ φ : Fin k → Fin n → α,
      Tt t (fun j => eta d (φ j)) = eta d (fun x => t (fun j => φ j x))) ∧
    ∀ R : Set (Fin n → α), PreservesRel t R → ClosedUnder t (V d R) := by sorry

end CSPIdealMem
