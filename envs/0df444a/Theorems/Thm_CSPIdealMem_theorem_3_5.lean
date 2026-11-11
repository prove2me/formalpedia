-- Prove2me | Theorems.Thm_CSPIdealMem_theorem_3_5
-- name    : CSPIdealMem.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:29:41.664734+00:00
-- url     : https://prove2.me/theorems/78dc9046-637e-4255-8c9a-e6b13746ec8f
-- title:
--   Theorem 3.5 — local reconstruction: projections on $\le 2d$ variables determine $V_d(R)$ and the evaluation span
-- statement:
--   Let $D\subseteq\mathbb Q$ be nonempty and finite and $R\subseteq D^X$. If $R$ is preserved by an idempotent cyclic operation of prime arity, then
--   $$
--   V_d(R)=\{z\in B_d\mid z_S\in V_S(R)\text{ for all }S,\ (z_S,z_T)\in V_{S,T}(R)\text{ for all }S\neq T\}.\tag{3.4}
--   $$
--   In particular, the projections of $R$ on at most $2d$ variables determine $V_d(R)$ and $\mathrm{span}_{\mathbb Q}\{\nu_d(\varphi)\mid\varphi\in R\}$: if $R$ and $R'$ are each preserved by an idempotent cyclic operation of prime arity and $\pi_UR=\pi_UR'$ for every $U\subseteq X$ with $|U|\le 2d$, then $V_d(R)=V_d(R')$ and the two numerical evaluation spans coincide.
--
--   This is the structural core of the polynomial-time algorithm.
--
--   Differences from the source:
--   - reading: "the projections of R on at most 2d variables determine V_d(R) and the span of its numerical degree-at-most-d evaluation vectors" → any two relations R, R′, each preserved by an idempotent cyclic operation of prime arity, with π_U R = π_U R′ for all |U| ≤ 2d, have V_d(R) = V_d(R′) and equal spans of ν_d; reason: "determine" means: is a function of these projections on the class of relations covered by the theorem
--   - encoding: V_{S,T}(R) spanned by (e_{a|S}, e_{a|T}) for a ∈ π_{S∪T} R → spanned by (e_{φ|S}, e_{φ|T}) for φ ∈ R; reason: the same set of generators
--   - encoding: T_t: the blockwise multilinear extension of t, defined on basis vectors by T_{t,S}(e_{a_1}, …, e_{a_k}) = e_{t(a_1, …, a_k)} and extended multilinearly (p.15) → the explicit formula T_t(z)_{S,b} = Σ_{a_1, …, a_k : t(a_1, …, a_k) = b} Π_j (z_j)_{S,a_j}; reason: this is the unique multilinear map with that action on basis vectors (checked on basis vectors in the sanity file)
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Theorem 3.5, p.21 (PDF 21)

import Mathlib
import Definitions.Def_CSPIdealMem_Indicator
import Definitions.Def_CSPIdealMem_EvalSpace

namespace CSPIdealMem

/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Theorem 3.5 (local reconstruction), p.21 (PDF 21).

(3.4) If `R ⊆ D^X` is preserved by an idempotent cyclic operation of prime arity, then
`V_d(R) = {z ∈ B_d | z_S ∈ V_S(R) for all S, (z_S, z_T) ∈ V_{S,T}(R) for all S ≠ T}`.
In particular, the projections of `R` on at most `2d` variables determine `V_d(R)` and the span of
its numerical degree-`≤ d` evaluation vectors: two such relations with the same projections on
every set of at most `2d` variables have the same `V_d` and the same `span_ℚ {ν_d(φ) | φ ∈ R}`. -/
theorem theorem_3_5 (D : Finset ℚ) (hD : D.Nonempty) (n d : ℕ) :
    (∀ R : Set (Fin n → D),
      (∃ (p : ℕ) (t : (Fin p → D) → D),
        p.Prime ∧ IsIdempotent t ∧ IsCyclic t ∧ PreservesRel t R) →
      (V d R : Set (Bd D n d)) =
        {z | (∀ S : Sd n d, z S ∈ VS R S) ∧
          ∀ S T : Sd n d, S ≠ T → (z S, z T) ∈ VST R S T}) ∧
    (∀ R R' : Set (Fin n → D),
      (∃ (p : ℕ) (t : (Fin p → D) → D),
        p.Prime ∧ IsIdempotent t ∧ IsCyclic t ∧ PreservesRel t R) →
      (∃ (p : ℕ) (t : (Fin p → D) → D),
        p.Prime ∧ IsIdempotent t ∧ IsCyclic t ∧ PreservesRel t R') →
      (∀ U : Finset (Fin n), U.card ≤ 2 * d → proj U R = proj U R') →
      V d R = V d R' ∧
        Submodule.span ℚ (assignVec d '' R) = Submodule.span ℚ (assignVec d '' R')) := by sorry

end CSPIdealMem
