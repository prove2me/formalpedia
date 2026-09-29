-- Prove2me | Theorems.Thm_FamousTheorems_schwartz_zippel
-- name    : FamousTheorems.schwartz_zippel
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:28.559238+00:00
-- url     : https://prove2.me/theorems/bbda8202-d3b0-4d22-b050-6ee0e167481e
-- title:
--   The Schwartz–Zippel lemma
-- statement:
--   **The Schwartz–Zippel lemma.** Let $p\ne0$ be a polynomial in $n$ variables over an integral domain $R$, and $S_1,\dots,S_n\subseteq R$ finite. Then
--   $$\frac{\#\{x\in S_1\times\cdots\times S_n : p(x)=0\}}{|S_1|\cdots|S_n|}\le\max_{s\in\operatorname{supp}p}\sum_i\frac{s_i}{|S_i|}.$$
--   In particular, with all $|S_i|=N$, a random point is a zero with probability at most $\deg p/N$.
--
--   It is the basis of randomized polynomial identity testing, with applications in algorithms (matchings, primality-style certificates), complexity (PCP, low-degree testing) and coding theory.
--
--   **Formalization note.** Mathlib's `MvPolynomial.schwartz_zippel_sup_sum`, in the sharp form using the support of $p$ (exponent vectors $s$) and values in `ℚ≥0`. The platform previously carried only a grid-induction step, not the lemma itself.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MvPolynomial.schwartz_zippel_sup_sum`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem schwartz_zippel {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {n : ℕ} {p : MvPolynomial (Fin n) R}
    (hp : p ≠ 0) (S : Fin n → Finset R) :
    (({x ∈ Fintype.piFinset fun i => S i | MvPolynomial.eval x p = 0}.card : NNRat) /
        ∏ i, ((S i).card : NNRat)) ≤
      p.support.sup fun s => ∑ i, ((s i : NNRat) / (S i).card) := by sorry

end FamousTheorems
