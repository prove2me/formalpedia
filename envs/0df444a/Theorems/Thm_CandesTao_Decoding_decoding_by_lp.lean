-- Prove2me | Theorems.Thm_CandesTao_Decoding_decoding_by_lp
-- name    : CandesTao.Decoding.decoding_by_lp
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-30T22:30:12.662984+00:00
-- url     : https://prove2.me/theorems/383b69dd-9c9e-4f68-b032-40e2d56de7fc
-- title:
--   Theorem 1.5: decoding by linear programming recovers the input from sparsely corrupted measurements
-- statement:
--   Let $A$ be a real $m \times n$ coding matrix with $m > n$ and full rank (the paper's standing assumption of Section 1.1), and let $F$ be a real $p \times m$ matrix such that $FA = 0$. Let $S \ge 1$ obey the hypothesis of Theorem 1.4 for $F$,
--   $$
--   \delta_S(F) + \theta_{S,S}(F) + \theta_{S,2S}(F) < 1 .
--   $$
--   Set $y = Af + e$, where $f \in \mathbb{R}^n$ is arbitrary and $e \in \mathbb{R}^m$ is a real vector supported on a set of size at most $S$. Then $f$ is the unique minimizer of
--   $$
--   (P_1') \qquad \min_{g \in \mathbb{R}^n} \|y - Ag\|_{\ell^1} .
--   $$
--
--   This is the decoding statement of the paper's title: with an annihilator $F$ of the code (any matrix with $FA = 0$, for instance the orthogonal projection onto the cokernel of $A$) obeying the restricted isometry condition, the plaintext $f$ is recovered exactly from the corrupted ciphertext $Af + e$ by solving one linear program, whatever the positions and values of the at most $S$ errors.
--
--   **Formalization Note** Full rank of the $m \times n$ matrix $A$ with $m > n$ is formalized as injectivity of $g \mapsto Ag$; the paper states $m > n$ and full rank once, in Section 1.1, and uses full rank to pass from the recovered error $e$ back to $f$. "Unique minimizer" means that every $g \ne f$ has strictly larger residual $\ell^1$ norm. The hypothesis $3S \le m$ is the domain on which Definition 1.1 defines $\theta_{S,2S}$.
-- source:
--   Candès--Tao 2005, Decoding by Linear Programming, IEEE Trans. Inform. Theory 51(12):4203-4215, doi:10.1109/TIT.2005.858979; arXiv:math/0502327v1 (https://arxiv.org/abs/math/0502327), p. 6, Theorem 1.5; standing assumptions m > n and A of full rank, p. 2, Section 1.1; equivalence of (P1) and (P1'), p. 4, Section 1.3

import Definitions.Def_CandesTao_Decoding_RestrictedIsometry
import Definitions.Def_CandesTao_Decoding_L1Minimization

namespace CandesTao.Decoding
theorem decoding_by_lp {p m n : ℕ} (hmn : n < m)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : Function.Injective A.mulVec)
    (F : Matrix (Fin p) (Fin m) ℝ) (hFA : F * A = 0) (S : ℕ)
    (hS : 1 ≤ S) (hSm : 3 * S ≤ m)
    (h : restrictedIsometryConst F S + restrictedOrthogonalityConst F S S +
      restrictedOrthogonalityConst F S (2 * S) < 1)
    (f : Fin n → ℝ) (e : Fin m → ℝ) (T : Finset (Fin m)) (hT : T.card ≤ S)
    (he : SupportedOn e T) :
    IsUniqueResidualL1Minimizer A (A.mulVec f + e) f := by sorry
end CandesTao.Decoding
