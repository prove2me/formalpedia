-- Prove2me | Theorems.Thm_FamousTheorems_banach_steinhaus
-- name    : FamousTheorems.banach_steinhaus
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T06:56:18.53099+00:00
-- url     : https://prove2.me/theorems/29fb43b1-6d63-4ecb-bb14-e1349ed08d1d
-- title:
--   The Banach–Steinhaus theorem
-- statement:
--   **The Banach–Steinhaus theorem**, or uniform boundedness principle.
--
--   Let $(g_i)_{i \in \iota}$ be a family of continuous linear maps from a Banach space $E$
--   to a normed space $F$. If the family is bounded at every point,
--   $$\forall x,\ \exists C,\ \forall i,\ \lVert g_i x\rVert \le C,$$
--   then it is uniformly bounded in operator norm:
--   $$\exists C',\ \forall i,\ \lVert g_i \rVert \le C'.$$
--
--   Pointwise information upgrades to uniform information for free. Nothing is assumed about
--   the index set — it may be uncountable — and the completeness of the *domain* is what makes
--   it work: the proof is a Baire category argument, writing $E$ as a countable union of the
--   closed sets where all $\lVert g_i x\rVert \le n$ and extracting an interior point.
--
--   Completeness is not decorative. On the incomplete space of finitely supported sequences the
--   functionals $x \mapsto n x_n$ are pointwise bounded but have unbounded norms.
--
--   Banach and Steinhaus published it in 1927, crediting Saks for the Baire-category proof.
--   Its standard consequences are that a pointwise limit of continuous linear maps is
--   continuous, and the existence of continuous functions whose Fourier series diverge at a
--   point.
--
--   **Formalization note.** `E →SL[σ₁₂] F` is the space of continuous $\sigma_{12}$-semilinear
--   maps, so the statement covers conjugate-linear operators as well. The result is Mathlib's
--   `banach_steinhaus`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open Filter Set Topology

theorem banach_steinhaus {E F 𝕜 𝕜₂ : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
    {ι : Type*} [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C' := by sorry

end FamousTheorems
