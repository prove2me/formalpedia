-- Prove2me | Theorems.Thm_BosonicLearn_gammaFock_weyl
-- name    : BosonicLearn.gammaFock_weyl
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:40:15.684262+00:00
-- url     : https://prove2.me/theorems/56cb5e69-2ced-42c6-a283-2776b7d0bab5
-- title:
--   Passive unitaries rotate displacements: $\Gamma(U)^\dagger D(z)\Gamma(U)=D(U^\dagger z)$ on Fock matrix elements
-- statement:
--   Covariance of the displacement (Weyl) operators under passive Gaussian unitaries.
--
--   Let $U$ be a unitary $n\times n$ matrix, $z\in\mathbb C^n$, and $D(z)_{ww'}=\prod_jD(z_j)_{w_jw'_j}$ the Fock matrix elements of the $n$-mode displacement operator. For all occupation vectors $u,v\in\mathbb N^n$,
--
--   $$
--   \sum_{|w|=|u|}\ \sum_{|w'|=|v|}\langle u|\Gamma(U^\dagger)|w\rangle\;D(z)_{ww'}\;\langle w'|\Gamma(U)|v\rangle=D(U^\dagger z)_{uv}.
--   $$
--
--   Role. $\Gamma(U)$ is the passive Gaussian unitary acting on the mode operators by $U$. With this identity the characteristic function of $\det(I-R)\Gamma(R)$ reduces, by diagonalizing $R$, to a product of single-mode thermal characteristic functions (`BosonicLearn.fugacity_characteristic`).
--
--   **Formalization Note** $\Gamma$ is `BosonicLearn.gammaFock` and $D(z)_{mn}$ is `Dependency50.P39.displacementMatrix`. $\Gamma$ preserves the total photon number, so both sums are finite; they are written over the box $w_i\le|u|$ filtered by $|w|=|u|$, as in `BosonicLearn.gammaFock_mul`. Unitarity is the hypothesis `Uᴴ * U = 1`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5 (Gaussian states, characteristic function, passive Gaussian states); Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R))

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open scoped Matrix

namespace BosonicLearn

/-- **Passive unitaries rotate displacements: `Γ(U)† D(z) Γ(U) = D(U†z)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, pp. 4–5 (displacement operators; passive Gaussian unitaries act on the mode operators by a unitary matrix); Lemma 2,
p. 20 (passive Gaussian states `det(I − R)Γ(R)`).

For a unitary `n × n` matrix `U`, amplitudes `z ∈ ℂⁿ` and occupation vectors `u, v`, with
`D(z)_{ww'} = ∏ⱼ D(zⱼ)_{wⱼ w'ⱼ}`,

`∑_{|w| = |u|} ∑_{|w'| = |v|} ⟨u|Γ(U†)|w⟩ D(z)_{ww'} ⟨w'|Γ(U)|v⟩ = D(U†z)_{uv}`.

**Formalization Note.** `Γ` preserves the total photon number, so both sums are finite; they are written over the
box `w_i ≤ |u|` filtered by `|w| = |u|`, as in `gammaFock_mul`. `D(z)_{mn}` is `Dependency50.P39.displacementMatrix`. -/
theorem gammaFock_weyl {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (z : Fin n → ℂ)
    (u v : Occupation (Fin n)) :
    ∑ w ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (∑ i, u i + 1)).filter
        (fun w => ∑ i, w i = ∑ i, u i),
      ∑ w' ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (∑ i, v i + 1)).filter
        (fun w' => ∑ i, w' i = ∑ i, v i),
        gammaFock Uᴴ u w * (∏ j, displacementMatrix (z j) (w j) (w' j)) * gammaFock U w' v =
      ∏ j, displacementMatrix ((Uᴴ *ᵥ z) j) (u j) (v j) := by sorry

end BosonicLearn
