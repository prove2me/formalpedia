-- Prove2me | Theorems.Thm_BosonicLearn_gammaFock_one_photon
-- name    : BosonicLearn.gammaFock_one_photon
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:12:19.347286+00:00
-- url     : https://prove2.me/theorems/5429d6b6-bebf-4395-aebd-f9fdd954c9df
-- title:
--   Vacuum and one-photon matrix elements of $\Gamma(R)$: $\langle0|\Gamma(R)|0\rangle=1$, $\langle e_i|\Gamma(R)|e_j\rangle=R_{ij}$
-- statement:
--   The lowest matrix elements of the second-quantization map.
--
--   For every $n\times n$ complex matrix $R$ and modes $i,j$:
--
--   $$
--   \langle0|\Gamma(R)|0\rangle=1,\qquad\langle e_i|\Gamma(R)|e_j\rangle=R_{ij},
--   $$
--
--   where $0$ is the vacuum occupation vector and $e_i$ the occupation vector with one photon in mode $i$.
--
--   Role. This is the formula $R=P_1\rho P_1/\operatorname{Tr}(P_0\rho)$ of Lemma 2 of the paper for $\rho=\det(I-R)\Gamma(R)$ (the one-photon sector identified with $\mathbb C^n$), which recovers the fugacity matrix from the state and gives the uniqueness of $R$.
--
--   **Formalization Note** $\Gamma$ is `BosonicLearn.gammaFock`; $e_i$ is `Pi.single i 1`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2, Eqs. (21)–(22), p. 20 ("R = P_1ρP_1/Tr(P_0ρ)")

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicLearn

/-- **Vacuum and one-photon matrix elements of `Γ(R)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, Eq. (22), p. 20: "if P_0 and P_1 denote the projectors onto the vacuum and one-photon sectors, respectively, then
R = P_1ρP_1/Tr(P_0ρ), where the one-photon sector is naturally identified with ℂⁿ."

For every `n × n` matrix `R`: `⟨0|Γ(R)|0⟩ = 1` and `⟨e_i|Γ(R)|e_j⟩ = R_ij`, where `e_i` is the occupation vector with
one photon in mode `i`.

**Formalization Note.** `e_i` is `Pi.single i 1`; `Γ` is `gammaFock`. -/
theorem gammaFock_one_photon {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    gammaFock R (0 : Occupation (Fin n)) 0 = 1 ∧
    gammaFock R (Pi.single i 1 : Occupation (Fin n)) (Pi.single j 1) = R i j := by sorry

end BosonicLearn
