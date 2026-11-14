-- Prove2me | Theorems.Thm_BosonicLearn_gammaFock_basic
-- name    : BosonicLearn.gammaFock_basic
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:08:33.475392+00:00
-- url     : https://prove2.me/theorems/03cb1b09-2076-47df-a7fb-232618dfd388
-- title:
--   Fock matrix of $\Gamma(A)$: particle-number conservation, $\Gamma(A^\dagger)=\Gamma(A)^\dagger$, $\Gamma(\mathbf 1)=\mathbf 1$
-- statement:
--   Three elementary properties of the Fock matrix elements of the second-quantization map $\Gamma$.
--
--   For an $n\times n$ complex matrix $A$ and occupation vectors $u,v\in\mathbb N^n$:
--
--   1. $\langle u|\Gamma(A)|v\rangle=0$ unless $|u|=|v|$ (total photon number is conserved);
--   2. $\langle u|\Gamma(A^\dagger)|v\rangle=\overline{\langle v|\Gamma(A)|u\rangle}$;
--   3. $\langle u|\Gamma(\mathbf 1)|v\rangle=\delta_{uv}$.
--
--   Role. Together with multiplicativity (`BosonicLearn.gammaFock_mul`) these make $\Gamma$ a $*$-homomorphism on each photon-number sector, which is what Lemma 2 of the paper uses to identify $\det(I-R)\Gamma(R)$ as a state.
--
--   **Formalization Note** $\Gamma(A)$ is the mission definition `BosonicLearn.gammaFock`, $\sqrt{u!\,v!}\sum_M\prod_{ij}A_{ij}^{M_{ij}}/M_{ij}!$ over $M\in\mathbb N^{n\times n}$ with row sums $u$ and column sums $v$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R))

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix

namespace BosonicLearn

/-- **Basic properties of `Γ`: sector structure, adjoint, identity.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, p. 20: "Γ(X) := ⊕_{m=0}^∞ Γ_m(X) and Γ_m(X) := X^{⊗m}|_{Sym^m(ℂⁿ)}, with Γ_0(X) := 1."

For an `n × n` complex matrix `A` and occupation vectors `u, v`: `⟨u|Γ(A)|v⟩ = 0` unless `|u| = |v|`;
`⟨u|Γ(A†)|v⟩ = conj ⟨v|Γ(A)|u⟩`; and `Γ(1) = 1`.

**Formalization Note.** `Γ` is `gammaFock`. -/
theorem gammaFock_basic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u v : Occupation (Fin n)) :
    (∑ i, u i ≠ ∑ i, v i → gammaFock A u v = 0) ∧
    gammaFock Aᴴ u v = star (gammaFock A v u) ∧
    gammaFock (1 : Matrix (Fin n) (Fin n) ℂ) u v = (if u = v then 1 else 0) := by sorry

end BosonicLearn
