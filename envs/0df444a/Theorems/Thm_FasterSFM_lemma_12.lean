-- Prove2me | Theorems.Thm_FasterSFM_lemma_12
-- name    : FasterSFM.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:41.570277+00:00
-- url     : https://prove2.me/theorems/fe36ba2d-8c02-401b-8922-f568cd39ab0e
-- title:
--   Lemma 12 — a thin event identifies a thin direction
-- statement:
--   Let $P$ be an admissible body, $S$ a subspace with orthonormal basis $J$, $z=Jy$ a certified center, $W=n+\lambda M$, and $b\in S$ a unit vector with $b^\top z\ge0$. Then the section lies in a Dikin-type ellipsoid around $z$:
--
--   $$P_S\ \subseteq\ z+\{u\in S:\ u^\top H_{\mathrm{fl}}(z)u\le(4W/\lambda)^2\}.$$
--
--   If $\upsilon=\sqrt{b^\top H_{\mathrm{fl}}(z)^{-1}b/\gamma}<\delta$, then
--
--   $$\mathrm{width}_b(P_S)=\max_{x\in P_S}b^\top x-\min_{x\in P_S}b^\top x\ \le\ \frac{8W\sqrt\gamma\,\delta}{\lambda},$$
--
--   and, when the number $k$ of inserted rows is at most $k_n$, this bound is $<1$ and some inserted row has a normal vector with nonzero projection onto $S$.
--
--   At a thin event the body is therefore very thin in the direction $b$, which feeds the certificate construction of §6.
--
--   Differences from the source:
--   - generalization: the oracle's lifted unit normal b → any unit b ∈ S with bᵀz ≥ 0; reason: the proof uses only these properties
--   - generalization: the current subspace S of block-constant vectors with its basis J = (ξ_C)_C (§5.1, p.16) → the column space of any J ∈ ℝ^{n×N} with JᵀJ = I; reason: the proof uses only that J has orthonormal columns; the block basis is an instance (reading R8)
--   - encoding: width_b(P_S) ≤ w → bᵀx − bᵀx' ≤ w for all x, x' ∈ P_S; reason: the definition of the width without sSup
--   - reading: the clauses "< 1" and "contains [an inserted row] with nonzero projection" (which use M ≤ M*, p.24) → explicit hypothesis k ≤ k_n on those clauses; reason: reading R7: Lemma 13's bound, which the algorithm supplies, made explicit
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 12, p.23

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier

namespace FasterSFM

open Classical Matrix

/-- **Lemma 12** (A thin event identifies a thin direction), p.23.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 12, p.23.

"At a certified center z = Jy, with W = n + λM, let the oracle return a nonzero vector, with lifted
unit normal b ∈ S and bᵀz ≥ 0. The current section is contained in the following ellipsoid:
P_S ⊆ z + {u ∈ S : uᵀH_fl(z)u ≤ (4W/λ)²}. If υ = √(bᵀH_fl(z)⁻¹b/γ) < δ then
width_b(P_S) ≤ 8W√γ δ/λ < 1 and the current set of inserted rows contains one whose normal vector has
nonzero projection onto S."

`width_b(P_S) = max_{x∈P_S} bᵀx − min_{x∈P_S} bᵀx` (p.23).

**Formalization Note.**
* Generalization: `b` is any unit vector of `S` with `bᵀz ≥ 0`; `S` any subspace (column space of `J`
  with `JᵀJ = I`, reading R8).
* `width_b(P_S) ≤ w` is stated as `bᵀx − bᵀx' ≤ w` for all `x, x' ∈ P_S`.
* Reading R7: the clauses "`< 1`" and "contains one [inserted row] whose normal vector has nonzero
  projection onto `S`" use `M ≤ M*` (proof, p.24, via Lemma 13); the number `k` of inserted rows
  `k ≤ k_n` is their explicit hypothesis. The containment and the width bound need no such
  hypothesis. -/
theorem lemma_12 {n N : ℕ} (P : Body n) (hP : P.Admissible) (J : Matrix (Fin n) (Fin N) ℝ)
    (hJ : Jᵀ * J = 1) (y : Fin N → ℝ) (hy : P.Certified J y) (b : Fin n → ℝ)
    (hbS : b ∈ colSpace J) (hb1 : b ⬝ᵥ b = 1) (hbz : 0 ≤ b ⬝ᵥ (J *ᵥ y)) :
    (∀ x ∈ colSpace J, P.Mem x →
      (x - J *ᵥ y) ⬝ᵥ (P.Hfl (J *ᵥ y) *ᵥ (x - J *ᵥ y)) ≤ (4 * P.W / lam) ^ 2) ∧
    (P.upsilon (J *ᵥ y) b < delta n →
      (∀ x ∈ colSpace J, P.Mem x → ∀ x' ∈ colSpace J, P.Mem x' →
        b ⬝ᵥ x - b ⬝ᵥ x' ≤ 8 * P.W * Real.sqrt gam * delta n / lam) ∧
      ((P.k : ℝ) ≤ kn n →
        8 * P.W * Real.sqrt gam * delta n / lam < 1 ∧
        ∃ i : Fin P.k, Jᵀ *ᵥ P.v i ≠ 0)) := by sorry

end FasterSFM
