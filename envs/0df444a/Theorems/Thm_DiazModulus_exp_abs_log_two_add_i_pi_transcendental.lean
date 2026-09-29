-- Prove2me | Theorems.Thm_DiazModulus_exp_abs_log_two_add_i_pi_transcendental
-- name    : DiazModulus.exp_abs_log_two_add_i_pi_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T11:03:27.420928+00:00
-- url     : https://prove2.me/theorems/eacad5a8-a6b8-4459-b59a-a3469e928686
-- title:
--   If log 2 is algebraic over ℚ(π), then exp √((log 2)² + π²) is transcendental
-- statement:
--   **The smallest open instance of Diaz's conjecture, seen from the homogeneous side.**
--
--   Suppose that $\log 2$ is algebraic over $\mathbb{Q}[i\pi]$; equivalently, $\log 2$ and $\pi$ are algebraically dependent. Then
--
--   $$\exp\sqrt{(\log 2)^{2}+\pi^{2}}$$
--
--   is transcendental.
--
--   The number $\sqrt{(\log 2)^{2}+\pi^{2}} = |\log 2 + i\pi|$ is the modulus of a logarithm of $-2$. Whether it is algebraic is the smallest open instance of Diaz's conjecture. This node says that it is not a logarithm of an algebraic number, provided $\log 2$ and $\pi$ are algebraically dependent. Whether they are is not known.
--
--   **Proof.** As in `DiazModulus.exp_abs_transcendental_of_conj_algebraic`, at $\lambda = \log 2 + i\pi$. Here $\lambda$ and $\bar\lambda = \log 2 - i\pi$ are both algebraic over $\mathbb{Q}[i\pi]$, so the entries of $\begin{pmatrix} |\lambda| & \bar\lambda \\ \lambda & |\lambda| \end{pmatrix}$ generate a field of transcendence degree one and `DiazModulus.four_exponentials_trdeg_one` applies.
--
--   **Attribution.** Known: this is the example that D. Roy and M. Waldschmidt give after their Corollaire 7.4, Ann. Sci. École Norm. Sup. (4) **30** (1997), p. 792. The contribution of this node is the formal proof.
-- source:
--   Known: D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, p. 792 (the example after Corollaire 7.4). Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem exp_abs_log_two_add_i_pi_transcendental (hdep : IsAlgebraic (↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ))) ((Real.log 2 : ℝ) : ℂ)) :
    Transcendental ℚ (Complex.exp ((Real.sqrt (Real.log 2 ^ 2 + Real.pi ^ 2) : ℝ) : ℂ)) := by
  sorry

end DiazModulus
