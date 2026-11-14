-- Prove2me | Theorems.Thm_BosonicLearn_gammaFock_mul
-- name    : BosonicLearn.gammaFock_mul
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:11:09.195774+00:00
-- url     : https://prove2.me/theorems/0cbe4276-74c5-4c5a-9f60-6f988dd88901
-- title:
--   $\Gamma$ is multiplicative on Fock matrix elements: $\langle u|\Gamma(AB)|v\rangle=\sum_{|w|=|u|}\langle u|\Gamma(A)|w\rangle\langle w|\Gamma(B)|v\rangle$
-- statement:
--   Functoriality of the second-quantization map $\Gamma$.
--
--   For $n\times n$ complex matrices $A,B$ and occupation vectors $u,v\in\mathbb N^n$,
--
--   $$
--   \langle u|\Gamma(AB)|v\rangle=\sum_{w\in\mathbb N^n,\ |w|=|u|}\langle u|\Gamma(A)|w\rangle\,\langle w|\Gamma(B)|v\rangle ,
--   $$
--
--   a finite sum over the sector of total photon number $|u|$.
--
--   Role. With `BosonicLearn.gammaFock_basic` this gives $\Gamma(S^\dagger S)=\Gamma(S)^\dagger\Gamma(S)\succeq0$ and $\Gamma(U\,\mathrm{diag}(d)\,U^\dagger)=\Gamma(U)\Gamma(\mathrm{diag}\,d)\Gamma(U)^\dagger$, the two facts behind Lemma 2 of the paper ($\det(I-R)\Gamma(R)$ is a state for Hermitian $0\preceq R\prec I$).
--
--   **Formalization Note** $\Gamma$ is `BosonicLearn.gammaFock`. The sum is written over the finite box $w_i\le|u|$ filtered by $|w|=|u|$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2 and Eq. (21), p. 20 (passive Gaussian states as det(I − R)Γ(R))

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicLearn

/-- **Second quantization is multiplicative: `Γ(AB) = Γ(A) Γ(B)`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, p. 20: "Γ(X) := ⊕_{m=0}^∞ Γ_m(X) and Γ_m(X) := X^{⊗m}|_{Sym^m(ℂⁿ)}, with Γ_0(X) := 1."

For `n × n` complex matrices `A, B` and occupation vectors `u, v ∈ ℕⁿ`,
`⟨u|Γ(AB)|v⟩ = ∑_w ⟨u|Γ(A)|w⟩ ⟨w|Γ(B)|v⟩`, the sum over the finitely many `w` with `|w| = |u|`.

**Formalization Note.** `Γ` is `gammaFock`; it vanishes between different photon-number sectors, so the sum over
all `w ∈ ℕⁿ` reduces to the sector of `u`, written as a filtered finite box. -/
theorem gammaFock_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Occupation (Fin n)) :
    gammaFock (A * B) u v =
      ∑ w ∈ (Fintype.piFinset fun _ : Fin n => Finset.range (∑ i, u i + 1)).filter
          (fun w => ∑ i, w i = ∑ i, u i),
        gammaFock A u w * gammaFock B w v := by sorry

end BosonicLearn
