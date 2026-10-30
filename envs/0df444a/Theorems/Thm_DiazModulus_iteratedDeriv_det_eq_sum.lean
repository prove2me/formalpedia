-- Prove2me | Theorems.Thm_DiazModulus_iteratedDeriv_det_eq_sum
-- name    : DiazModulus.iteratedDeriv_det_eq_sum
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:32.191987+00:00
-- url     : https://prove2.me/theorems/4b91dc89-dfa7-42b9-a1d1-a34ab9e6a9eb
-- title:
--   Leibniz rule for a determinant of entire functions: its $j$-th derivative is a multinomial sum of determinants whose column $\mu$ is differentiated $q_\mu$ times
-- statement:
--   Let $g_{l\mu}$ ($l, \mu \in \{1, \dots, L\}$) be entire functions, $j \in \mathbb{N}$ and $z \in \mathbb{C}$. Then the $j$-th derivative of $x \mapsto \det(g_{l\mu}(x))$ at $z$ is $\sum_q \frac{j!}{\prod_\mu q_\mu!} \det(g_{l\mu}^{(q_\mu)}(z))$, the sum over the $q \in \mathbb{N}^L$ with $\sum_\mu q_\mu = j$: column $\mu$ is differentiated $q_\mu$ times.
--
--   **Proof.** Expand the determinant over permutations. By linearity it suffices to differentiate a product $\prod_\mu h_\mu$ of entire functions; the general Leibniz rule $(\prod_\mu h_\mu)^{(j)} = \sum_{\sum q = j} \binom{j}{q} \prod_\mu h_\mu^{(q_\mu)}$ is proved by induction on $L$, splitting off the factor $\mu = 0$, applying the binomial Leibniz rule and the induction hypothesis, and reindexing the double sum through $q \mapsto (q_0, (q_1, \dots))$, with $\binom{j}{(i, q')} = \binom{i + |q'|}{i}\binom{|q'|}{q'}$. Exchanging the sums over permutations and over $q$ gives the statement.
--
--   **Novelty.** Classical; routine formalisation. The Leibniz rule, applied column by column; it is used in the proof of DALAG Lemma 9.2.
-- source:
--   Classical (the Leibniz rule for products). Used for M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 9.2. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem iteratedDeriv_det_eq_sum {L : ℕ} (g : Fin L → Fin L → ℂ → ℂ) (hg : ∀ l μ, Differentiable ℂ (g l μ))
    (j : ℕ) (z : ℂ) :
    iteratedDeriv j (fun x => (Matrix.of fun l μ => g l μ x).det) z =
      ∑ q ∈ Finset.Nat.antidiagonalTuple L j, (Nat.multinomial Finset.univ q : ℂ) *
        (Matrix.of fun l μ => iteratedDeriv (q μ) (g l μ) z).det := by
  sorry

end DiazModulus
