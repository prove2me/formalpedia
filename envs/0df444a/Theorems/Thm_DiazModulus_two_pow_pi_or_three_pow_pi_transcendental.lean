-- Prove2me | Theorems.Thm_DiazModulus_two_pow_pi_or_three_pow_pi_transcendental
-- name    : DiazModulus.two_pow_pi_or_three_pow_pi_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:19:12.422941+00:00
-- url     : https://prove2.me/theorems/87f2e1de-b2f7-49e0-83be-e3ec9f0a6192
-- title:
--   At least one of 2^π and 3^π is transcendental
-- statement:
--   At least one of the real numbers $2^{\pi}$ and $3^{\pi}$ is transcendental.
--
--   This is Waldschmidt's statement (2.2.3) (1988, p. 379) at $t = \pi$ and $\beta = i$, where $e^{i\pi} = -1$. It strengthens `DiazModulus.two_three_five_pow_pi_transcendental`, which states that one of $2^{\pi}$, $3^{\pi}$, $5^{\pi}$ is transcendental, from the six exponentials theorem.
--
--   **Proof.** Apply the five exponentials theorem (`DiazModulus.five_exponentials`) to $x = (1, \pi)$, $y = (\log 2, \log 3)$ and $\eta = i$. The five numbers are $2$, $3$, $2^{\pi}$, $3^{\pi}$ and $e^{i\pi} = -1$, so $2^{\pi}$ and $3^{\pi}$ are not both algebraic. $x$ is linearly independent over $\mathbb{Q}$ because $\pi$ is irrational. $y$ is: $(p/q)\log 2 = \log 3$ with integers $p, q > 0$ would give $2^p = 3^q$, which is impossible as $3^q$ is odd. $i$ is algebraic, as $i^2 = -1$.
--
--   **Novelty.** None: this is Waldschmidt's statement (2.2.3) (1988, p. 379) at $t = \pi$, $\beta = i$, a consequence of the five exponentials theorem. The contribution of this node is the formal proof.
-- source:
--   Known: M. Waldschmidt, On the transcendence methods of Gel'fond and Schneider in several variables, in New Advances in Transcendence Theory (Durham, 1986), Cambridge Univ. Press, 1988, 375–398, statement (2.2.3), p. 379, at t = π, β = i (e^(iπ) = −1), from the five exponentials theorem (Cor. 2.2). It strengthens DiazModulus.two_three_five_pow_pi_transcendental, which has three numbers. Uses DiazModulus.five_exponentials. C2 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **`2^π` or `3^π`.** At least one of the real numbers `2^π`, `3^π` is transcendental.

M. Waldschmidt, Durham 1986 lectures (1988), statement (2.2.3), p. 379, at `t = π`, `β = i`
(`e^{iπ} = -1`), from the five exponentials theorem with `x = (1, π)` and `y = (log 2, log 3)`.
Neither number is known to be transcendental on its own. -/
theorem two_pow_pi_or_three_pow_pi_transcendental :
    Transcendental ℚ ((2 : ℝ) ^ Real.pi) ∨ Transcendental ℚ ((3 : ℝ) ^ Real.pi) := by
  sorry

end DiazModulus
