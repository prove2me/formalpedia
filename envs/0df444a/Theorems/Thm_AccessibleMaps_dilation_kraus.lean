-- Prove2me | Theorems.Thm_AccessibleMaps_dilation_kraus
-- name    : AccessibleMaps.dilation_kraus
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:15.622832+00:00
-- url     : https://prove2.me/theorems/78c2c22e-ad8e-4414-9d09-138002372ec4
-- title:
--   Eq. (15): $\sigma\mapsto\operatorname{tr}_B[U(\sigma\otimes\omega)U^\dagger]$ has a trace-preserving Kraus form
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space, $\omega$ a density operator on $\mathcal H$ and $U$ a unitary on $\mathbb C^{a}\otimes\mathcal H$. Then there are finitely many $a\times a$ matrices $M_1,\dots,M_N$ such that for **every** $a\times a$ complex matrix $\sigma$
--   $$
--   \operatorname{tr}_B\big[U(\sigma\otimes\omega)U^\dagger\big]=\sum_{k=1}^N M_k\,\sigma\,M_k^\dagger,
--   \qquad\text{and}\qquad \sum_{k=1}^N M_k^\dagger M_k=\mathbb 1 .
--   $$
--   So the product term of the decomposition (14) yields a trace-preserving completely positive map in the Kraus form (1)–(2).
--
--   This is the CP half of the affine form of an accessible map.
--
--   Differences from the source:
--   - generalization: finite-dimensional systems (p.1), with the infinite-dimensional ancilla treated only in the proof of Proposition 1 → the ancilla H is any complex Hilbert space, with no finite dimension or separability; reason: the proof of Proposition 1 treats the infinite-dimensional case; finite-dimensional H is a special case
--   - generalization: Kraus operators M_μν indexed by pairs μν (an infinite family when H is infinite-dimensional) → a finite Kraus family M : Fin N → Matrix a a ℂ; reason: a finite family is a countable one (pad with zeros); finiteness is the stronger statement and holds since the system is finite-dimensional
--   - generalization: the identity (15) for the state ρ_A → the identity for every a × a complex matrix σ; reason: the map is linear; a density matrix is a special case
--   - encoding: Fano coefficients α, β, γ, Γ and SU(d) generators σ_i^A, σ_j^B → coordinate-free operators on the block space C^a ⊗ H (PiLp 2), with tr_A, tr_B blockwise; reason: generators have no finite form for infinite-dimensional H; the operator form has the same instances
-- source:
--   Carteret, Terno & Życzkowski, Dynamics beyond completely positive maps, arXiv:quant-ph/0512167v3, Eq. (15), p.3, and "The CP-map term is trace-preserving", p.4

import Mathlib
import Definitions.Def_HayashiHoeffding_IsDensityOp
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_AccessibleMaps_tensorOp
import Definitions.Def_AccessibleMaps_reducedEvolution

open HayashiHoeffding PeresTerno

namespace AccessibleMaps

variable {a H : Type*} [Fintype a] [DecidableEq a] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- For a density operator `ω` on `H` and a unitary `U` on the composite space, the map
`σ ↦ tr_B [U (σ ⊗ ω) U†]` on all matrices has a finite Kraus form `σ ↦ ∑ₐ Mₐ σ Mₐ†` with
`∑ₐ Mₐ† Mₐ = 𝟙`.

Carteret, Terno & Życzkowski, arXiv:quant-ph/0512167v3, Eq. (15), p.3 (PDF p.3), and "The CP-map term is
trace-preserving", p.4 (PDF p.4).

**Formalization Note.** The family in (15) is indexed by pairs `μν` and is infinite when `H` is
infinite-dimensional. The system is finite-dimensional, so a finite family exists, and that stronger
form is asserted. The identity holds for every matrix `σ`, not only for density matrices. -/
theorem dilation_kraus (ω : H →L[ℂ] H) (hω : IsDensityOp ω)
    (U : unitary (Composite a H →L[ℂ] Composite a H)) :
    ∃ (N : ℕ) (M : Fin N → Matrix a a ℂ),
      (∀ σ : Matrix a a ℂ, reducedEvolution U (tensorOp σ ω) = krausUpdate M σ) ∧
        povmElement M = 1 := by sorry

end AccessibleMaps
